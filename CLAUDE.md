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
- Do not commit or push unless I ask (or the checklist tells you to). Commit directly on
  `master`; never create a new branch. When you commit, keep yourself as a co-author (the
  `Co-Authored-By` line) unless I explicitly say otherwise.
- Do not add "written by AI" comments to code; I decide where to put them.
- If you notice a pattern in my commands (e.g. I keep asking for the same kind of task, or
  keep giving the same correction), you may suggest an instruction to add to this file.
  Only suggest it, with the proposed wording; never add it yourself. I decide whether it
  is worth adding.

## IMPORTANT: always check for `eqToIso` / `eqToHom`
This is extremely important. Check it EVERY time, for every Lean task (a `to claude` command,
finishing or cleaning up a proof, writing a definition, answering a question about code, ...),
BEFORE you start working on it:
- Look for `eqToIso` / `eqToHom` in the code involved: the term itself, AND the project
  definitions it uses or unfolds (e.g. if a proof is about `basechange_over_Field.trans`, check
  how `basechange_over_Field.trans` is defined).
- If you find any, STOP and flag it to me first, with file and line, and suggest an explicit
  construction instead (e.g. `Over.isoMk` with the hom and inverse given by `pullback.lift`).
  Do not work around it (e.g. with helper lemmas) without asking me.
- Also flag it immediately if, while working, you hit a kernel `deterministic timeout` or run out
  of memory and `eqToIso` / `eqToHom` may be the cause.
- Never introduce `eqToIso` / `eqToHom` yourself.

Why: `eqToHom h` is the identity transported along `h`, so when a proof unfolds it (e.g. `simp`
with only `rfl`-lemmas, whose proof is just `id`), the kernel must check the two sides of `h`
definitionally equal, e.g. `Spec.map (ofHom (algebraMap K K))` and `𝟙 (Spec ↧K)`, by unfolding
the construction of `Spec`. This runs out of memory or times out. (`basechange_over_Field.refl`
was originally defined with `eqToIso`, and `simp [refl]` ran out of memory; `eqToIso` in
`basechange_over_Field.trans` caused kernel timeouts.)

## `to claude` comments
- I sometimes leave instructions for you as comments in the code, of the form
  `-- to claude: ...` (spacing and capitalisation may vary, e.g. `to claude : ...`).
  A `to claude` command always *begins* with `to claude` (right after the comment marker).
  A comment that only mentions it later (e.g. "when executing the to claude command, put the
  def here") is not a command; it is a note belonging to a command, so follow it while
  executing that command, and do not count it when checking how many commands there are.
- Do not act on them by yourself. Only act when I tell you to execute a
  `to claude` command.
- Comments of the form `Hey claude, ...` are NOT `to claude` commands: they are notes for
  discussion. Never act on them; at most mention them or remind me of them, and wait for an
  explicit command before any edit.
- When I do, first search every file of the project (excluding `.lake/` and
  `.git/`) for all `to claude` comments, case-insensitively:
      grep -rni "to claude" --exclude-dir=.lake --exclude-dir=.git .
  - If there is more than one, do NOT execute any of them. Inform me, listing
    each one with its file and line.
  - If there is exactly one, first check that the file containing it has no unsaved
    changes in VS Code (otherwise I cannot see your edits). VS Code keeps a backup of each
    unsaved file in `~/.config/Code/Backups/`, whose first line is the file's URI:
        grep -rlF "file://$(realpath <FILE>) " ~/.config/Code/Backups 2>/dev/null
    If this prints anything, do not execute the command: tell me the file is unsaved and
    ask me to save it first.
    The same applies to every other file you edit while executing the command (which
    needs my permission, see below): run the check on it before editing it, and if it
    has unsaved changes, stop and ask me to save it first.
  - Otherwise, follow it. Executing it counts as permission to make
    the edits that instruction asks for (and only those).
  - Keep all new code (including helper lemmas) in the file containing the command, unless
    the command says otherwise. If you strongly feel that something belongs elsewhere
    (e.g. `ForMathlib/`), ask me before putting it there.
  - If the command asks for a construction inside a proof (e.g. "define `f` to be the
    isomorphism ..."), build it inside that proof as a `let`/`have`; do not add a new
    top-level `def`/`lemma`, not even a general one. If a top-level helper really seems better,
    suggest it and ask first.
  - Once it has been executed, delete the `to claude` comment itself.
  - If the instruction asks for a term (e.g. "is there something that gives ...?") and you
    find one, but I did not explicitly say how to edit the file, you may answer it in the
    file with `#check`s:
    - a single `#check` goes in place of the `to claude` comment, with no extra empty lines;
    - several `#check`s go together in place of the comment, with at least 3 empty lines
      above and below the group (not necessarily between them), so that they stand out;
    - write `#check foo`, not `#check @foo` (use `@` only when explicit arguments are needed,
      e.g. `#check @foo _ ℤ`).

## Solving a `sorry` with helper lemmas
When I ask you to solve a `sorry` and allow helper lemmas:
- Put the helper terms in the same file as the result being proved, as far as possible (see
  "Keep all new code ... in the file containing the command" above).
- Helper lemmas may be left as `sorry` if you cannot prove them.
- When done, list every helper term you created, with its file, in the order in which they appear.
- If your changes cause errors you cannot fix, either delete or comment out everything you added
  (your choice), and tell me explicitly which you did, so that I can delete anything left as a
  comment.

## Working with subagents
- When I ask you to work on a proof or definition, act as the leader: keep your own context
  clean and spawn up to three subagents to finish it (how many, and which models, depends on
  the difficulty; use stronger models for harder tasks). The agents must keep you updated,
  especially when they hit a timeout.
- Use Fable only for extremely hard tasks. Whenever you use it (spawning an agent with it, or
  giving an existing Fable agent a new task), tell me which agent and which task. This is only
  to inform me: do not ask for or wait for my approval.
- Subagents never edit project files. They test their work in copies in your scratchpad
  directory. When an agent has a finished change, it sends you the exact text and where it
  goes. Your only job is to paste it in with the Edit tool, unchanged, so that the change
  shows up in this chat; do not check or build it yourself. Then tell the agent the edit is
  in, and the agent builds the module and reports whether it compiles (and fixes it the same
  way if it does not). Agents send only the lines that change (enough surrounding text to
  locate them uniquely), not the whole proof, especially for fixes.
- Agents give the line number with each change, and you read only the few lines around it
  (`Read` with offset/limit) before editing, never the whole file.
- Agent updates are one or two lines (what is done, what is blocking); no proof states, error
  logs or sketches unless you ask for them.
- Brief agents by pointing at file, line and name rather than pasting code, and send
  follow-ups to the same agent with SendMessage instead of spawning a new one.

## `Pick up from here` comments
- I sometimes leave a note for where to resume work, as a comment of the form
  `-- Pick up from here : ...` (spacing and capitalisation may vary). Like a `to claude`
  command, it always *begins* with `Pick up from here` (right after the comment marker).
- At the start of every session, before doing anything else (even before the task in my
  first message), search the project for them, case-insensitively:
      grep -rni "pick up from here" --exclude-dir=.lake --exclude-dir=.git .
  (ignore the hits in this file), and tell me about every one you find, with its file, line
  and text. Then continue with my first message.
- Only notify me: do not act on it, edit it or delete it unless I tell you to.

## Building
- Lean toolchain and Mathlib version: see `lean-toolchain` / `lakefile.toml`.
- Build everything: `lake build`
- Build one module: `lake build CMAbelianVarieties.Path.To.File`
- Regenerate `CMAbelianVarieties.lean` (imports every library file): `lake exe mk_all`
- `relaxedAutoImplicit = false` and the Mathlib standard linter set are enabled.

## Pushing
Whenever I ask you to push, do it in a new terminal window. Do not try to push yourself: you do
not have my GitHub credentials. Open a new terminal window that runs the push with my username
already filled in, so that I only have to enter my token. If a push fails (e.g. I mistype the
token), it tries again, up to 3 attempts in total. It writes the result to a log file in your
scratchpad directory (`<LOG>` below):
    gnome-terminal --working-directory="$(git rev-parse --show-toplevel)" -- bash -c '
      for i in 1 2 3; do
        git -c credential.username=abhijitaj1997 push && { r=0; break; }
        r=1; [ $i -lt 3 ] && echo "Push failed, trying again (attempt $((i+1)) of 3)"
      done
      echo "PUSH FINISHED (exit $r)" | tee <LOG>; exec bash'
(Run this from inside the project; the project path differs between my computers, so do not
hard-code it.)
Tell me when the window has been opened. Then, without waiting for me to say anything, wait in
the background for the `PUSH FINISHED` line to appear in the log, check with
    git status -sb
that master is no longer ahead of origin/master, and tell me the result: either that the push
succeeded, or that all 3 attempts failed (in which case I can read the error in the terminal
window).

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
- Avoid `eqToIso` / `eqToHom`: see "IMPORTANT: always check for `eqToIso` / `eqToHom`" above.
- Never make global (section) variables explicit: declare them implicit, `variable {F : ...}`,
  never `variable (F : ...)` (instance arguments stay `[...]`). If a single declaration needs one
  of them explicit, use `variable (F) in` directly above that declaration only.

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
