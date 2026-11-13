# An import only `Lib`'s types name: no body of an edited module uses a
# template of it, so no description step of one reads its inventories.
Base := { tag : Str }.{
    make : Str -> Base
    make = |s| { tag: s }

    tag_of : Base -> Str
    tag_of = |b| b.tag
}
