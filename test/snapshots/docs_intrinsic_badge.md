# META
~~~ini
description=An intrinsic, a declaration with a type and no body, carries a badge in the documentation
type=docs
~~~
# SOURCE
## app.roc
~~~roc
app [main] { pf: platform "./platform.roc" }

import Mail

main = Mail.shout("hello")
~~~
## Mail.roc
~~~roc
Mail := {}.{
    ## Whether the text is an email address. A translator gives it a meaning.
    is_email : Str -> Bool

    shout : Str -> Str
    shout = |text| text.concat("!")
}
~~~
## platform.roc
~~~roc
platform ""
    requires {} { main : Str }
    exposes []
    packages {}
    provides { "roc_main": main_for_host }
    targets: {
        inputs_dir: "targets/",
        x64glibc: { inputs: [app] },
    }

main_for_host : Str
main_for_host = main
~~~
# DOCS
~~~clojure
(package-docs
  (name "test-app")
  (mod
    (name "Mail")
    (package "app")
    (kind type_mod)
    (entry
      (name "Mail")
      (kind nominal)
      (type "Mail := " (record))
      (entry
        (name "is_email")
        (kind value)
        (type (fn (type-ref (name "Str")) (type-ref (name "Bool"))))
        (badge "intrinsic: no Roc body")
        (doc "Whether the text is an email address. A translator gives it a meaning.")
      )
      (entry
        (name "shout")
        (kind value)
        (type (fn (type-ref (name "Str")) (type-ref (name "Str"))))
      )
    )
  )
  (mod
    (name "app")
    (package "app")
    (kind app)
    (entry
      (name "main")
      (kind value)
      (type (type-ref (name "Str")))
    )
  )
)
~~~
