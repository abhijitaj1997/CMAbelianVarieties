# CMAbelianVarieties: instructions for Claude Code

## About the project
A Lean 4 + Mathlib formalisation of CM abelian varieties. The goal is to prove
that a CM abelian variety over an algebraically closed field of characteristic 0
(together with its CM structure) has a model over a number field. The statement
lives in `CMAbelianVarieties/Theorem.lean` (not yet proven).

## Ground rules
- **Do NOT edit, create, move or delete any file unless I specifically tell you
  to.** If you think a change would help, describe it and suggest it instead.
  An explicit task (e.g. "run the checklist") permits only the edits that task covers.
- Do not commit or push unless I ask (or the checklist tells you to).
- If you write a proof or definition, mark it with a comment directly above it
  saying it was written by AI (see "AI usage" in README.md).

## `to claude` comments
- I sometimes leave instructions for you as comments in the code, of the form
  `-- to claude: ...` (spacing and capitalisation may vary, e.g. `to claude : ...`).
- Do not act on them by yourself. Only act when I tell you to execute a
  `to claude` command.
- When I do, first search every file of the project (excluding `.lake/` and
  `.git/`) for all `to claude` comments, case-insensitively:
      grep -rni "to claude" --exclude-dir=.lake --exclude-dir=.git .
  - If there is more than one, do NOT execute any of them. Inform me, listing
    each one with its file and line.
  - If there is exactly one, follow it. Executing it counts as permission to make
    the edits that instruction asks for (and only those).
  - Once it has been executed, delete the `to claude` comment itself.

## Building
- Lean toolchain and Mathlib version: see `lean-toolchain` / `lakefile.toml`.
- Build everything: `lake build`
- Build one module: `lake build CMAbelianVarieties.Path.To.File`
- Regenerate `CMAbelianVarieties.lean` (imports every library file): `lake exe mk_all`
- `relaxedAutoImplicit = false` and the Mathlib standard linter set are enabled.

## Updating Mathlib
When I ask you to update Mathlib, do the following in the project root, in order.
1. Fetch Mathlib's current toolchain:
       curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
2. Keep `lakefile.toml` in sync with it (otherwise `lake update` keeps the old Mathlib
   and the build fails). Read the new version `<VER>` from `lean-toolchain` (the part
   after `leanprover/lean4:`, e.g. `v4.36.0-rc1`) and check that Mathlib has a tag for it:
       git ls-remote --tags https://github.com/leanprover-community/mathlib4 refs/tags/<VER>
   - If the tag exists, set `rev = "<VER>"` in the mathlib `[[require]]` block of
     `lakefile.toml`, and tell me the old and new version.
   - If it does not exist, stop and ask me what to do (do not run `lake update`).
3. Run the slow commands, in this order:
       lake update          # new Mathlib source + lake-manifest.json
       lake exe cache get   # prebuilt Mathlib files (always run it, even though
                            # `lake update` sometimes does this automatically)
       lake exe mk_all      # regenerate CMAbelianVarieties.lean
       lake build
   I want to see progress bars wherever possible, so run them in a new terminal window
   that I can watch live. Use `script` so they still see a real terminal (I keep the
   progress bars and estimated time left) while the output is recorded to a log file
   in your scratchpad directory (`<LOG>` below):
       gnome-terminal --working-directory="$(git rev-parse --show-toplevel)" -- bash -c '
         script -q -e -c "lake update && lake exe cache get && lake exe mk_all && lake build" <LOG>; \
         echo "MATHLIB UPDATE FINISHED (exit $?)" | tee -a <LOG>; \
         exec bash'
   (Run this from inside the project; the project path differs between my
   computers, so do not hard-code it.)
   Tell me when the window has been opened. Then wait for the
   `MATHLIB UPDATE FINISHED` line to appear in the log, strip the terminal control
   codes from it, read it, and report the outcome to me: which command it stopped at
   if one failed, and any errors. Only report build errors; do not fix them unless I
   ask.
4. Check that `lean-toolchain`, the `rev` in `lakefile.toml`, and the mathlib entry in
   `lake-manifest.json` all agree on `<VER>`, and tell me if they do not.

Asking you to update Mathlib counts as permission for the file changes these steps
make (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `CMAbelianVarieties.lean`).

## Layout
- `CMAbelianVarieties/`: the library
  - `Defn.lean`, `Theorem.lean`: main definitions and the main theorem
  - `AbstractNonsense/`: category theory (group objects, pullbacks, End rings)
  - `AlgebraicGeometry/`: schemes, Lie algebras, abelian varieties, homomorphisms
  - `preCMType/`: pre-CM types and field representations
  - `ForMathlib/`: results that could be upstreamed to Mathlib
  - `Catalogue.lean` files: `#check` cheat sheets, not real content
- `Test/`: scratch/test files, outside the library (not imported by mk_all)
- `Pondering/`: notes

## Bookkeeping files
- `CMAbelianVarieties/ToDo`: unfinished results (still `sorry`). Only pending
  tasks belong here; completed tasks are removed.
- `MindMap.md`: Mermaid diagram of imports between project files.
- `ClaudeCodeChecklist`: the end-of-session checklist. When I say "run the
  checklist", follow it step by step, exactly.
  - Whenever you notice uncommitted changes to `ClaudeCodeChecklist`, check that
    its note still says to print `Checklist complete!` with the summary right after
    the last main step (the final build and commit), and not after an on-request
    step such as the push or at a stale step number. If it is out of date, tell me
    and suggest the fix.

## Lean conventions
- Follow Mathlib style and naming conventions.
- Keep imports minimal: import the smallest Mathlib/project file that suffices.
- When searching for Mathlib results, report the exact name and file.
- Avoid `eqToIso` / `eqToHom` in definitions and statements (e.g. to identify base changes along
  equal morphisms of schemes); construct the morphisms explicitly instead (e.g. via
  `pullback.lift`). Reason: `eqToHom h` is the identity transported along `h`, so when a
  proof unfolds it (e.g. `simp` with only `rfl`-lemmas, whose proof is just `id`), the kernel
  must check the two sides of `h` definitionally equal, e.g. `Spec.map (ofHom (algebraMap K K))`
  and `𝟙 (Spec ↧K)`, by unfolding the construction of `Spec`. This runs out of memory or times
  out. (`basechange_over_Field.refl` was originally defined with `eqToIso`, and `simp [refl]`
  ran out of memory.)
  Whenever you notice `eqToIso` or `eqToHom` in code I wrote (or am asking you about), flag
  it to me, with file and line, and suggest an explicit construction instead.

## Cleaning up a term
When I ask you to clean up a term (a `def`, `lemma`, `theorem`, `instance`, etc.), tidy
its body so that it would be admissible in Mathlib:
- **Do not rewrite the proof from scratch.** Fundamentally, the proof idea must still be
  the one I have written down. Keep my proof's structure and strategy: the same overall
  argument and the same definitions/data. Case splits may be shortened (e.g. merged or
  handled with `<;>`), but not removed entirely in favour of a different proof route.
  Clean it up step by step (merge redundant tactic steps, use the right lemma names, drop
  unnecessary wrappers like `id (Eq.symm _)`, etc.). If you think a different approach
  would be much better, suggest it and ask, rather than doing it.
- Follow Mathlib's conventions and idioms. Do not use unusual tricks that Mathlib would not
  use, even if they would shorten the code massively.
- Remove `let`s and `have`s that are not needed, and shorten the code into something
  readable and well structured. This includes `let`s and `have`s that are used (e.g. by
  inlining them), as long as the idea and fundamental steps of the proof are not changed.
- Do not change the term's name or statement unless I ask.
- A clean-up request does not mean you have to change anything. If the term is already
  clean and you do not recommend changing it, say so (without editing it); I will then tell
  you what I think.
- Afterwards, build the module and confirm there are no new errors or warnings.
