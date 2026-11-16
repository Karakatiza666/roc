# Composable Platforms

A proposal to let a Roc application compose one **root platform** with any number
of **platform extensions**, so that native functionality can be added to a
platform without forking it.

Status: design sketch. Independent of, but complementary to,
`roc-reify-proposal.md`.

---

## 1. Summary

Every Roc application is built on exactly one platform, and that platform
provides all of the application's native functionality. The rule is load-bearing
and this proposal does not change it. What it changes is that a platform stops
having to be a single indivisible artifact.

```roc
app [main!] {
	pf:   platform  "…/basic-cli.tar.zst",      # root: owns main() and the allocator
	gpu:  extension "…/cuda-runtime.tar.zst",   # contributes effects and link inputs
	dbsp: extension "…/dbsp-runtime.tar.zst",
}
```

A root platform opts into composition by naming where extension link inputs go.
A platform that does not opt in cannot be composed, and the question never
arises. Native code still arrives only through a platform, so the security model
keeps its shape: no new category of trusted component, no escape hatch, no
`unsafe`.

---

## 2. The problem

### 2.1 Platform-specific packages are pinned to one exact build

The langref already supports packages that depend on a platform, and already
states the cost:

> When an application uses a platform-specific package, every platform
> declaration in the dependency graph must identify exactly the same platform.
> For URL dependencies this includes the declared version and content hash;
> ordinary compatible-version upgrades do not apply to platform selection.

So a package built on `basic-webserver` 1.2.0 with hash X works with that build
and nothing else. Not 1.2.1. Not a fork with one extra effect. An ecosystem of
reusable platform-dependent packages cannot form under that constraint, because
every package pins the whole application to one artifact.

### 2.2 Platforms reimplement the same primitives

Stdout, stderr, environment variables, filesystem, clock, random, process exit.
Every platform implements them, in its own host language, with its own bugs,
because there is no way to share a host implementation. The Roc API can be
copied; the native half cannot.

### 2.3 Adding a runtime means forking a platform

An application that wants a GPU compute runtime, a database driver, or an
incremental computation engine, on top of an ordinary CLI or webserver platform,
has exactly one option today: fork the platform and merge the two hosts. Then
fork it again for the next combination. The number of artifacts needed is the
product of the choices, not the sum.

This is the constraint that makes several otherwise-reasonable designs
impractical, and it is worth fixing on its own merits.

---

## 3. Non-goals

- **Not** changing who may ship native code. Only platforms may, before and
  after.
- **Not** making platforms interchangeable. An app still targets one root, and a
  package written for a CLI root still does not work on a WebAssembly root.
- **Not** effect polymorphism. No change to `->` and `=>`.
- **Not** sandboxing. An extension's native code is trusted exactly as a
  platform's native code is trusted today. Section 7 is explicit about this.
- **Not** multiple entry points. Exactly one root owns `main()`.

---

## 4. The model

| | Root platform | Extension |
|---|---|---|
| Per application | Exactly one | Any number, including zero |
| Owns `main()` and program start | Yes | No |
| Owns `roc_alloc` / `roc_dealloc` / `roc_panic` | Yes | No |
| Has a `requires` section | Yes | No, in v1 |
| `exposes` type modules to the app | Yes | Yes |
| `provides` hosted symbols | Yes | Yes |
| Has a `targets` block | Yes | Yes, listing only its own inputs |
| Decides whether composition happens | Yes | No |

An extension is a platform that gave up the entry point, the allocator and the
`requires` clause, and kept everything else. That is a small enough delta that it
could share the `platform` header with one extra marker rather than needing a new
module kind, which section 5 explores.

---

## 5. Syntax

### Option A. A keyword in the app header—recommended

```roc
app [main!] {
	pf:   platform  "…/basic-cli.tar.zst",
	dbsp: extension "…/dbsp-runtime.tar.zst",
}
```

Symmetric with `platform`, unambiguous about which is root, and it reads. The
extension's own header marks it:

```roc
extension "dbsp-runtime"
	exposes [Rel, Engine]
	provides { "roc__dbsp_start": start! }
	targets : {
		inputs_dir: "targets/",
		x64linux: { inputs: ["libdbsp_runtime.a"] },
	}
```

No `requires`, no `main`, no `crt1.o`, no `app` placeholder. Those belong to the
root.

### Option B. The root names its extensions

```roc
platform "basic-cli-plus"
	requires { main! : … }
	extensions { dbsp: "…/dbsp-runtime.tar.zst" }
```

Perfect control, but it is not composition: the platform author has to have
anticipated the combination, which is the problem restated. Useful as a way for a
platform to ship a curated bundle, not as the mechanism.

### Option C. No new keyword; an extension is a platform without `requires`

```roc
app [main!] {
	pf:   platform "…/basic-cli.tar.zst",
	dbsp: platform "…/dbsp-runtime.tar.zst",
}
```

The root is whichever one has a `requires` section the app satisfies. Fewer
concepts, but "which of these is the root" becomes an inference rather than a
declaration, and two artifacts with `requires` become an error the reader has to
reason about. Reject.

### The gate falls out of the existing `targets` syntax

A root opts into composition by saying where extension inputs go in its link
order, using a new placeholder alongside the existing `app` one:

```roc
platform "basic-cli"
	…
	targets : {
		inputs_dir: "targets/",
		x64linux: { inputs: ["crt1.o", "host.o", extensions, app] },
		wasm32:   { inputs: ["host.wasm", app], exports: ["run"] },
	}
```

Three properties make this the right gate:

- **Opting out is the default.** A platform with no `extensions` placeholder
  cannot be composed. No new header field, no policy language, no migration.
  A safe-scripting platform stays exactly as safe as it is today by doing nothing.
- **Link order stays the root's decision**, which matters and which only the root
  can know.
- **It is per target.** A platform can accept extensions on native targets and
  refuse them on `wasm32`, which is the same kind of per-target reasoning the
  block already expresses.

---

## 6. Semantics

**Entry point.** The root's host owns `main()`. Extensions contribute no entry
point and are never started by the compiler.

**Allocator.** The root provides `roc_alloc`, `roc_dealloc` and `roc_panic`.
An extension must not. Where an extension's native dependencies want a global
allocator of their own, they have to be built to route through the root's, or the
root has to be the one choosing that allocator. This is a real constraint, it is
the kind of thing the langref already says platforms decide, and it should be
documented rather than discovered at link time.

**Initialization.** No implicit init hook in v1. An extension that needs setup
does it lazily inside its own first effectful call, which keeps program start
entirely the root's.

**Symbol names.** The langref notes that hosted functions and `provides`
entrypoints are identified by the symbol strings in the header, never by module
content. Two extensions naming the same symbol therefore collide at link time.
The fix is to namespace an extension's provided symbols by its declared name or
content hash, and to report a collision as a build error naming both artifacts
rather than as a linker diagnostic.

**Linking.** Each extension's `targets` block lists only its own inputs. The
build concatenates them, in app-header order, at the root's `extensions`
placeholder. An extension that has no entry for the selected target is a build
error naming the target.

**Type identity.** Unchanged. Nominal type identity is content-based, and hosted
declarations are identified by symbol string, so an extension's types behave like
any platform's.

**Purity.** Unchanged. An extension's effects are `=>` like any platform's, and
its exposed pure modules are pure like any package's.

---

## 7. Trust, stated plainly

An extension's native code is trusted exactly as a platform's native code is
trusted. It can open sockets whatever its documentation says. Roc has no
mechanism to confine it and this proposal does not add one.

What changes is the count. Roc today has one trusted native component per
application. After this, it has one plus however many extensions the app names.
Three things keep that from being a meaningful weakening:

1. **The root decides whether it is possible at all.** A platform whose point is
   confinement omits the placeholder and is unaffected.
2. **The set is explicit and small.** Every extension is a line in the app
   header, visible to any reader and to any audit, unlike a transitive
   dependency.
3. **It is still bounded.** Rust trusts every crate in the graph. Roc would trust
   a root plus a handful of named extensions.

A later refinement could have the root declare a grant set and extensions declare
needs, so a mismatch is a build error. That would be documentation and audit, not
enforcement, and it is not needed for v1.

---

## 8. What this does not solve

- An app still cannot be written against "any platform that has stdout". This
  proposal lets a platform be assembled; it does not make platform APIs
  interchangeable.
- Version skew between a root and an extension built against different libc or
  compiler assumptions is a real failure mode, and the content-hash pinning that
  causes 2.1 is also what makes it detectable. Composition trades one problem for
  a smaller one, not for none.
- Extensions cannot require values from the app, so anything shaped like the
  `[Model : model] for main` pattern stays the root's job.

---

## 9. Interaction with reified code

`roc-reify-proposal.md` defines a translator as a compiler written in pure Roc
that runs at build time and produces data. Most translators need nothing from
this proposal: a shader compiler's output is bytes, and a GPU kernel or a SQL
query is executed by a platform that already owns the device or the connection.

The case that needs this proposal is an ordinary app, on a platform the author
did not write, that needs a native engine the platform does not carry. Without
composition the only options are forking the platform or letting a package ship
native code, and the second would be Roc's first escape hatch from "all native
code arrives through the platform".

So the two proposals are separable and should be argued separately. Reification
does not depend on composition, composition does not depend on reification, and
the combination is what makes the hardest use cases reachable without weakening
anything.

---

## 10. Open questions

**Should an extension be able to depend on another extension?** A DAG of
extensions is a natural request and a natural source of diamond problems. v1 says
no: extensions are leaves, and an app names all of them.

**Should extensions have `requires`?** Some genuinely want an app-provided value
(a config, a model type). v1 says no, because it interacts with the root's own
`requires` in ways worth deferring.

**Per-target availability.** An extension with no `wasm32` entry should fail the
build clearly; whether it should instead make the app silently unbuildable for
that target is a policy question.

**Dynamic versus static extension inputs.** A large native runtime is often
better as a shared object than as a static archive, and the existing `output`
field already distinguishes artifact kinds. Whether extensions can be dynamically
loaded, and what that means for a hermetic build, is unresolved.

**Does this subsume the platform-specific package?** If a package can be shipped
as an extension exposing pure modules plus hosted effects, the pinned-hash rule
in 2.1 may be able to relax for packages that go that route. Worth exploring; not
assumed here.

---

## 11. Sequencing

1. **The `extensions` placeholder and the `extension` header**, with static
   archive inputs only and no init hook. Enough to link a second host into an
   app.
2. **Symbol namespacing and collision diagnostics**, which is where the first
   real bugs will be.
3. **A shared primitives extension** as the proof: stdout, env, clock,
   filesystem, implemented once and composed into two different roots. This
   directly attacks 2.2 and is the cheapest way to find out whether the model
   holds.
4. **Grant declarations**, if and when the audit story needs them.

Step 3 is the one that decides whether this is worth having, and it involves no
reification, no GPU and no database.
