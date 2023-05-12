use ide_db::source_change::SourceChangeBuilder;
use syntax::{
    ast::{self, HasName, HasVisibility},
    AstNode,
    SyntaxKind::{
        CONST, ENUM, FN, MACRO_DEF, MODULE, STATIC, STRUCT, TRAIT, TYPE_ALIAS, USE, VISIBILITY,
    },
    SyntaxNode, T,
};
use text_edit::{TextSize, TextRange};

use crate::{utils::vis_offset, AssistContext, AssistId, AssistKind, Assists};

// Assist: change_visibility
//
// Adds or changes existing visibility specifier.
//
// ```
// $0fn frobnicate() {}
// ```
// ->
// ```
// pub(crate) fn frobnicate() {}
// ```
pub(crate) fn change_visibility(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    if let Some(vis) = ctx.find_node_at_offset::<ast::Visibility>() {
        if let Some(vis_parent) = vis.syntax().parent() {
            let target = vis.syntax().text_range();
            change_vis(acc, Some(vis), &vis_parent, Some(target));
        }
        return None;
    } else {
        add_vis(acc, ctx)
    }
}

fn add_vis(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let item_keyword = ctx.token_at_offset().find(|leaf| {
        matches!(leaf.kind(),
            | T![const]
            | T![static]
            | T![fn]
            | T![mod]
            | T![struct]
            | T![enum]
            | T![trait]
            | T![type]
            | T![use]
            | T![macro])
    });

    if let Some(keyword) = item_keyword {
        let parent = keyword.parent()?;
        let def_kws =
            vec![CONST, STATIC, FN, MODULE, STRUCT, ENUM, TRAIT, TYPE_ALIAS, USE, MACRO_DEF];
        // Parent is not a definition, can't add visibility
        if !def_kws.iter().any(|&def_kw| def_kw == parent.kind()) {
            return None;
        }
        // Already have visibility, do nothing
        if parent.children().any(|child| child.kind() == VISIBILITY) {
            return None;
        }
        change_vis(acc, None, &parent, Some(keyword.text_range()))
    } else if let Some(field_name) = ctx.find_node_at_offset::<ast::Name>() {
        let field = field_name.syntax().ancestors().find_map(ast::RecordField::cast)?;
        if field.name()? != field_name {
            cov_mark::hit!(change_visibility_field_false_positive);
            return None;
        }
        if field.visibility().is_some() {
            return None;
        }
        change_vis(acc, None, field.syntax(), Some(field_name.syntax().text_range()))
    } else if let Some(field) = ctx.find_node_at_offset::<ast::TupleField>() {
        if field.visibility().is_some() {
            return None;
        }
        change_vis(acc, None, field.syntax(), None)
    } else {
        return None;
    }
}

fn change_vis(
    acc: &mut Assists,
    vis: Option<ast::Visibility>,
    vis_parent: &SyntaxNode,
    target: Option<TextRange>,
) -> Option<()> {

    let target = target.unwrap_or_else(|| vis_parent.text_range());
    let (vis_kind, offset_or_range) = if let Some(vis) = &vis {
        let vis_kind = VisibilityKind::try_from(vis).ok()?;
        let text_range = vis.syntax().text_range();
        (Some(vis_kind), OffsetOrRange::Range(text_range))
    } else {
        (None, OffsetOrRange::Offset(vis_offset(vis_parent)))
    };

    if vis_kind != Some(VisibilityKind::Pub) {
        acc.add(
            AssistId("change_visibility", AssistKind::RefactorRewrite),
            "Change visibility to pub",
            target,
            |edit| {
                insert_or_replace(edit, offset_or_range, VisibilityKind::Pub);
                promote_ancestors(edit, vis_parent, VisibilityKind::Pub);
            }, 
        )?;
    }

    if vis_kind != Some(VisibilityKind::PubCrate) {
        acc.add(
            AssistId("change_visibility", AssistKind::RefactorRewrite),
            "Change visibility to pub(crate)",
            target,
            |edit| {
                insert_or_replace(edit, offset_or_range, VisibilityKind::PubCrate);
                if vis_kind.map(|vk| vk < VisibilityKind::PubCrate).unwrap_or(true) {
                    promote_ancestors(edit, vis_parent, VisibilityKind::PubCrate);
                } else {
                    demote_descendants(edit, vis.as_ref(), vis_parent, VisibilityKind::PubCrate);
                }
            },
        )?;
    }

    let can_super = vis_parent.ancestors()
        .filter_map(ast::Module::cast)
        .nth(if vis_parent.kind() == MODULE { 1 } else { 0 })
        .is_some();

    if can_super && vis_kind != Some(VisibilityKind::PubSuper) {
        acc.add(
            AssistId("change_visibility", AssistKind::RefactorRewrite),
            "Change visibility to pub(super)",
            target,
            |edit| {
                insert_or_replace(edit, offset_or_range, VisibilityKind::PubSuper);
                if vis_kind.map(|vk| vk < VisibilityKind::PubSuper).unwrap_or(true) {
                    promote_ancestors(edit, vis_parent, VisibilityKind::PubSuper);
                } else {
                    demote_descendants(edit, vis.as_ref(), vis_parent, VisibilityKind::PubSuper);
                }
            },
        )?;
    }

    #[derive(Clone, Copy)]
    enum OffsetOrRange { Offset(TextSize), Range(TextRange) }
    fn insert_or_replace(
        edit: &mut SourceChangeBuilder,
        offset_or_range: OffsetOrRange,
        vis_kind: VisibilityKind
    ) {
        match offset_or_range {
            OffsetOrRange::Offset(offset) => edit.insert(offset, format!("{} ", vis_kind.as_str())),
            OffsetOrRange::Range(range) => edit.replace(range, vis_kind.as_str()),
        }
    }

    /// Simplifies working with visibilities within this module.
    /// `pub(in some::path)` is omitted because the complexity it introduces.
    #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
    enum VisibilityKind { PubSelf, PubSuper, PubCrate, Pub }

    impl<'v> TryFrom<&'v ast::Visibility> for VisibilityKind {
        type Error = Option<String>; // An invalid path (e.g. `pub(in some::path)` or pub(invalid)`)
        fn try_from(vis: &'v ast::Visibility) -> Result<Self, Self::Error> {
            if vis.syntax().text() == "pub" { return Ok(VisibilityKind::Pub) }
            let Some(path) = vis.path() else { return Err(None) };
            match (vis.in_token(), path.syntax().text()) {
                (None, path) if path == "crate" => Ok(VisibilityKind::PubCrate),
                (None, path) if path == "super" => Ok(VisibilityKind::PubSuper),
                (None, path) if path == "self" => Ok(VisibilityKind::PubSelf),
                (_, invalid_path) => Err(Some(invalid_path.to_string())),
            }
        }
    }

    impl VisibilityKind {
        fn as_str(&self) -> &'static str {
            match self {
                VisibilityKind::PubSelf => "pub(self)",
                VisibilityKind::PubSuper => "pub(super)",
                VisibilityKind::PubCrate => "pub(crate)",
                VisibilityKind::Pub => "pub",
            }
        }
    }

    fn promote_ancestors(
        edit: &mut SourceChangeBuilder,
        vis_parent: &SyntaxNode,
        new_visibility_kind: VisibilityKind,
    ) {
        if vis_parent.kind() != STRUCT {
            if let Some(strukt) = vis_parent.ancestors().find_map(ast::Struct::cast) {
                if !promote(edit, &strukt, new_visibility_kind) { return }
            }
        }

        if new_visibility_kind == VisibilityKind::PubSuper { return }

        let skip = if vis_parent.kind() == MODULE { 1 } else { 0 };
        for module in vis_parent.ancestors().skip(skip).filter_map(ast::Module::cast) {
            if !promote(edit, &module, new_visibility_kind) { break }
        }

        fn promote(
            edit: &mut SourceChangeBuilder,
            node: &(impl AstNode + HasVisibility + std::fmt::Debug),
            new_visibility_kind: VisibilityKind,
        ) -> bool {
            if let Some(vis) = node.visibility() {
                if VisibilityKind::try_from(&vis).map(|vk| vk >= new_visibility_kind)
                    .unwrap_or(true) { return false }
                edit.replace(vis.syntax().text_range(), new_visibility_kind.as_str());
            } else {
                edit.insert(vis_offset(node.syntax()), format!("{} ", new_visibility_kind.as_str()));
            }
            true
        }
    }

    fn demote_descendants(
        edit: &mut SourceChangeBuilder,
        vis: Option<&ast::Visibility>,
        vis_parent: &SyntaxNode,
        new_visibility_kind: VisibilityKind,
    ) {
        for vis in vis_parent.descendants()
            .filter_map(ast::Visibility::cast)
            .filter(|v| vis.map(|vis| v != vis).unwrap_or(true)) {
            if !matches!(VisibilityKind::try_from(&vis), Ok(vk) if vk > new_visibility_kind) { continue }
            edit.replace(vis.syntax().text_range(), new_visibility_kind.as_str());
        }
    }

    Some(())
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_by_label, check_assist_not_applicable, check_assist_target};

    use super::*;

    #[test]
    fn change_visibility_adds_pub_crate_to_items() {
        check_assist(change_visibility, "$0fn foo() {}", "pub(crate) fn foo() {}");
        check_assist(change_visibility, "f$0n foo() {}", "pub(crate) fn foo() {}");
        check_assist(change_visibility, "$0struct Foo {}", "pub(crate) struct Foo {}");
        check_assist(change_visibility, "$0mod foo {}", "pub(crate) mod foo {}");
        check_assist(change_visibility, "$0trait Foo {}", "pub(crate) trait Foo {}");
        check_assist(change_visibility, "m$0od {}", "pub(crate) mod {}");
        check_assist(change_visibility, "unsafe f$0n foo() {}", "pub(crate) unsafe fn foo() {}");
        check_assist(change_visibility, "$0macro foo() {}", "pub(crate) macro foo() {}");
        check_assist(change_visibility, "$0use foo;", "pub(crate) use foo;");
    }

    #[test]
    fn change_visibility_works_with_struct_fields() {
        check_assist(
            change_visibility,
            r"struct S { $0field: u32 }",
            r"pub(crate) struct S { pub(crate) field: u32 }",
        );
        check_assist(
            change_visibility,
            r"struct S ( $0u32 )",
            r"pub(crate) struct S ( pub(crate) u32 )"
        );
    }

    #[test]
    fn change_visibility_field_false_positive() {
        cov_mark::check!(change_visibility_field_false_positive);
        check_assist_not_applicable(
            change_visibility,
            r"struct S { field: [(); { let $0x = ();}] }",
        )
    }

    #[test]
    fn change_visibility_pub_to_pub_crate() {
        check_assist(change_visibility, "$0pub fn foo() {}", "pub(crate) fn foo() {}")
    }

    #[test]
    fn change_visibility_pub_crate_to_pub() {
        check_assist(change_visibility, "$0pub(crate) fn foo() {}", "pub fn foo() {}")
    }

    #[test]
    fn change_visibility_const() {
        check_assist(change_visibility, "$0const FOO = 3u8;", "pub(crate) const FOO = 3u8;");
    }

    #[test]
    fn change_visibility_static() {
        check_assist(change_visibility, "$0static FOO = 3u8;", "pub(crate) static FOO = 3u8;");
    }

    #[test]
    fn change_visibility_type_alias() {
        check_assist(change_visibility, "$0type T = ();", "pub(crate) type T = ();");
    }

    #[test]
    fn change_visibility_handles_comment_attrs() {
        check_assist(
            change_visibility,
            r"
            /// docs

            // comments

            #[derive(Debug)]
            $0struct Foo;
            ",
            r"
            /// docs

            // comments

            #[derive(Debug)]
            pub(crate) struct Foo;
            ",
        )
    }

    #[test]
    fn change_visibility_adds_super_within_mod() {
        check_assist(
            change_visibility,
            r"mod foo { m$0od bar {} }",
            r"mod foo { pub(super) mod bar {} }",
        );
        check_assist(
            change_visibility,
            r"mod foo { s$0truct S; }",
            r"mod foo { pub(super) struct S; }",
        );
        check_assist(
            change_visibility,
            r"mod foo { struct S(($0)); }",
            r"mod foo { pub(super) struct S(pub(super) ()); }",
        );
        check_assist(
            change_visibility,
            r"mod foo { struct S { b$0ar: () } }",
            r"mod foo { pub(super) struct S { pub(super) bar: () } }",
        );
        check_assist(
            change_visibility,
            r"mod foo { pub struct S { b$0ar: () } }",
            r"mod foo { pub struct S { pub(super) bar: () } }",
        );
        check_assist_by_label(
            change_visibility,
            r"mod foo { struct S { b$0ar: () } }",
            r"pub mod foo { pub struct S { pub bar: () } }",
            "Change visibility to pub",
        );
    }

    #[test]
    fn change_visibility_demotions() {
        check_assist(
            change_visibility,
            r"p$0ub mod foo { pub m$0od bar {} }",
            r"pub(crate) mod foo { pub(crate) mod bar {} }",
        );
    }

    #[test]
    fn not_applicable_for_enum_variants() {
        check_assist_not_applicable(
            change_visibility,
            r"mod foo { pub enum Foo {Foo1} }
              fn main() { foo::Foo::Foo1$0 } ",
        );
    }

    #[test]
    fn change_visibility_target() {
        check_assist_target(change_visibility, "$0fn foo() {}", "fn");
        check_assist_target(change_visibility, "pub(crate)$0 fn foo() {}", "pub(crate)");
        check_assist_target(change_visibility, "struct S { $0field: u32 }", "field");
    }
}
