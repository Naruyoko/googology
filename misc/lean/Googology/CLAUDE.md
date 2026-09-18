# PUCS-1(2) Formalization

## Project Description

We are formalizing a proof based on @Googology/PUCS_1_2/japanese_proof.wikitext in @Googology/PUCS_1_2/pucs_1_2.lean.

The Lean file should follow the rough steps of the informal proof in the wikitext. Do not look at other Lean files, as they are unrelated to this proof.

## Task

You will be given a task later, which will be supplied with the `/goal` command. If there are existing errors, they might not be the task. Do not start working until then.

Work autonomously. There is a recommended workflow below.

## Tool Policy

Do not use bash commands. Use Lean LSP MCP tools to your fullest. Understand its capabilities. For example, they allow you to:

- See the file outline (`lean_file_outline`)
- Check proof state at any position (`lean_goal`)
- View expected types (`lean_term_goal`)
- Inspect symbol types and documentation (`lean_hover_info`)
- Get compiler diagnostics and warnings (`lean_diagnostic_messages`)
- Search for local declarations (`lean_local_search`)
- Test multiple tactics without modifying code (`lean_multi_attempt`)
- Get quick fixes and suggested actions (`lean_code_actions`)
- Search Mathlib using natural language (`lean_leansearch`)
- Search Mathlib by type patterns (`lean_loogle`)

*Note*: Some tools may time out on first use, because the first build takes a long time.

## Editing Files

Make each edit small, so you know exactly which edits you make are creating/solving errors. Each edit must contain at most 1 tactic. This means that an edit can either: add 1 tactic, remove 1 tactic, or change 1 tactic. Examples of a tactic is `rw`, `apply`, `exact`, `simp`, `linearith`, and `calc`. If a large change is needed, build it step-by-step using temporary `sorry`s. You must use the Edit tool, not the Write tool or shell commands such as `sed`.

Pay attention to indentation, as Lean is sensitive to it.

## Required Workflow

1. Run `lean_file_outline` and `lean_diagnostic_messages` on the entire file to identify all errors and warnings
2. Use `lean_goal`, `lean_term_goal`, and `lean_hover_info` to understand the proof state at that position
3. Search applicable lemmas in local declarations (`lean_local_search`) and Mathlib (`lean_leansearch` (natural language) or `lean_loogle` (type patterns))
4. Make a small, targeted, step-by-step edit. Do not make multiple edits at once.
5. After each edit, re-check with `lean_goal` and `lean_diagnostic_messages` to verify progress
6. When stuck, use `lean_multi_attempt` to test alternative tactics

Use additional MCP tools, detailed above, as necessary.

## Quality Requirements

The Lean file should compile without errors, and all proofs should be correct, verifiable by Lean, and as concise as possible while maintaining mathematical clarity and correctness.

## Postword

Acknowledge the user that you understand the instructions, the limitations, the tools available, and the workflow.
