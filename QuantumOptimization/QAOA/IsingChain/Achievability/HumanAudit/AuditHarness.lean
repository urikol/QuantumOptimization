import Mathlib.Init  -- registers the Mathlib linter options the lakefile sets globally
import Lean
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Data.Html

/-!
# Audit-harness commands — `#auditPrint` and `#audit_gate`

Reusable infrastructure for the human-audit files under `HumanAudit/`. This module defines
two commands and is itself mark-free (it always compiles), so it is safe to keep in the
manifest; the audit *content* files that invoke these commands stay out of the manifest
(they error by design until fully audited).

* **`#auditPrint`** — placed after `#print <name>` on the same line, shows a panel listing the
  *audited declarations* `<name>` visibly references — i.e. those that have their own
  `#print … #auditPrint` line in this file — each tagged green ✓ if its line is `[x]` or red ✗
  otherwise, and each a link to that line. It is a *static* widget (panel `Html` computed at
  elaboration, rendered by the pure-JS `HtmlDisplayPanel`), so it makes no server RPC call and
  never triggers a restart-time `Task.get` panic.

* **`#audit_gate`** — scans the file's `AUDIT-REGION` and errors until every item is `[x]`,
  so a green build certifies a complete audit.

Both commands locate audit items by scanning the *current* source (`getFileMap`), i.e. the
live editor buffer, so they reflect edits as the relevant command re-elaborates; they work
identically under `lake env lean`.
-/

open Lean Server Elab Command ProofWidgets
open scoped Json

/-- If `l` is a `#print`/`#auditPrint` line, return the printed name. -/
def printLineName? (l : String) : Option String :=
  match (l.splitOn " ").filter (· != "") with
  | kw :: nm :: _ => if kw == "#print" || kw == "#auditPrint" then some nm else none
  | _ => none

/-- Props for `revealLink`: a document `uri` and a `range` to reveal. -/
structure RevealLinkProps where
  uri : String
  range : Lsp.Range
  deriving FromJson, ToJson

/-- A pure-JS link that, on click, reveals `range` of `uri` via the InfoView's
`revealLocation` — and *nothing else*. (`MakeEditLink` instead does `applyEdit` first and only
navigates if that resolves; a null-version `applyEdit` rejects, so navigation never runs. By
calling `revealLocation` directly we avoid `applyEdit` entirely.) JS mirrors `makeEditLink.js`
with the `applyEdit` step removed. -/
@[widget_module]
def revealLink : Component RevealLinkProps where
  javascript := "import{jsx as e}from\"react/jsx-runtime\";import*as t from\"react\";\
import{EditorContext as i}from\"@leanprover/infoview\";\
function n(n){const o=t.useContext(i);\
return e(\"a\",{className:\"link pointer dim \",\
onClick:async()=>{await o.revealLocation({uri:n.uri,range:n.range})},children:n.children})}\
export{n as default};"

/-- The maximal qualified-identifier tokens of `s` (runs of letters/digits/`_`/`.`/`'`). Used
to match audit names as *whole* names — so `Quantum.Operators.Ket` is not falsely matched just
because `Quantum.Operators.Ket.dag` occurs. -/
def identTokens (s : String) : Std.HashSet String := Id.run do
  let mut toks : Std.HashSet String := {}
  let mut cur : String := ""
  for c in s.toList do
    if c.isAlphanum || c == '.' || c == '_' || c == '\'' then
      cur := cur.push c
    else if cur != "" then
      toks := toks.insert cur; cur := ""
  if cur != "" then toks := toks.insert cur
  return toks

/-- A clickable link that reveals the **end** of `line` (0-based) of `uri`. `lineText` is that
line's content; the end column is its UTF-16 length (computed via `Lsp.Position.advance`). -/
def auditNavLink (uri : String) (line : Nat) (lineText : String) (label : Html) : Html :=
  let endPos : Lsp.Position := (⟨line, 0⟩ : Lsp.Position).advance lineText.toRawSubstring
  Html.ofComponent revealLink { uri := uri, range := ⟨endPos, endPos⟩ } #[label]

/-- `#auditPrint`, placed after `#print <name>` on the same line, shows a panel listing the
*audited declarations* `<name>` visibly references — each green ✓ if its line is `[x]` or red ✗
otherwise, and each a link to that line.

A name is "referenced" if it is an audit item (has a `#print … #auditPrint` line in this file)
and appears as a whole identifier token in the *pretty-printed* declaration — its type and
(for non-theorems) value, plus, for a structure, its constructor type (where the field types
live). For a theorem the value is its *proof*, which is not scanned — a statement-level audit
reads only the statement, so only the type contributes references. Printing uses
`pp.fullNames` and `pp.fieldNotation false`, so constants and projections both show as full
names (`A.B.proj x`, not `x.proj`) and can be matched; implicit/instance arguments stay hidden,
so names buried there (e.g. `NQubitDim` inside a matrix-mul instance) are excluded. This is
deliberately *what `#print` shows*, not `Expr.getUsedConstants` (which would also surface those
hidden dependencies). -/
elab "#auditPrint" : command => do
  let ref ← getRef
  let fm ← getFileMap
  let lines := fm.source.splitOn "\n" |>.toArray
  let thisLine := (fm.toPosition (ref.getPos?.getD default)).line - 1   -- 0-based
  let nameStr ← match printLineName? ((lines[thisLine]?).getD "") with
    | some s => pure s
    | none => throwError "#auditPrint must follow `#print <name>` on the same line"
  let name := nameStr.toName
  -- name → (0-based line, audited?)
  let mut info : Std.HashMap String (Nat × Bool) := {}
  for i in [0:lines.size] do
    match printLineName? lines[i]! with
    | some nm => info := info.insert nm (i, (lines[i]!.splitOn "[x]").length > 1)
    | none => pure ()
  -- `pp.fullNames` so referenced constants print as full names (matchable against the audit
  -- list); `pp.fieldNotation false` so projections print as `A.B.proj x` (full name) rather
  -- than `x.proj`, so they're matched too. Implicit/instance args stay hidden, so this is
  -- still "what's displayed" (e.g. `NQubitDim`, buried in instance args, does not appear).
  let bodyStr ← liftTermElabM <|
    withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.fieldNotation false) do
      let env ← getEnv
      let ci ← match env.find? name with
        | some ci => pure ci
        | none => throwError s!"#auditPrint: unknown constant {name}"
      let mut parts : Array String := #[toString (← Meta.ppExpr ci.type)]
      -- For a THEOREM, the "value" is its proof term — not part of the statement a human
      -- audits, and it can surface proof-internal constants that are not statement-level
      -- dependencies. Scan the value only for non-theorems (defs/instances), whose body IS
      -- audited; for a theorem, scan only its type (the statement).
      unless (ci matches .thmInfo ..) do
        if let some e := ci.value? then
          parts := parts.push (toString (← Meta.ppExpr e))
      -- For a structure/inductive the field types live in the constructor type(s).
      if let .inductInfo info := ci then
        for ctor in info.ctors do
          if let some cinfo := env.find? ctor then
            parts := parts.push (toString (← Meta.ppExpr cinfo.type))
      pure (String.intercalate "\n" parts.toList)
  let toks := identTokens bodyStr
  let refs := ((info.toList.map (·.1)).filter fun s => s != name.toString && toks.contains s).eraseDups
  let uri := "file://" ++ (← getFileName)
  let items : Array Html := (refs.filterMap fun r =>
    (info[r]?).map fun (i, audited) =>
      let mark :=
        if audited then
          Html.element "span" #[("style", json% {color: "green", fontWeight: "bold"})] #[.text "✓ "]
        else
          Html.element "span" #[("style", json% {color: "red", fontWeight: "bold"})] #[.text "✗ "]
      Html.element "li" #[] #[mark, auditNavLink uri i (lines[i]!) (.text r)]).toArray
  let ht : Html :=
    if items.isEmpty then Html.element "span" #[] #[.text "(no project-local references)"]
    else Html.element "div" #[] #[
      Html.element "b" #[] #[.text "references:"],
      Html.element "ul" #[] items]
  liftCoreM <| Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← rpcEncode ht) }) ref

/-- `#audit_gate` scans the file's `AUDIT-REGION` and errors until every item is `[x]`:
both `[ ]` (unaudited) and `[!]` (flagged) keep it red. It reads the live source
(`getFileMap`), so the count refreshes as you type a mark, and works under `lake env lean`.
The sentinel/mark literals are written split so these gate lines — outside the scanned
region anyway — are never miscounted. -/
elab "#audit_gate" : command => do
  let region := (((← getFileMap).source.splitOn ("AUDIT-REGION" ++ "-START")).getD 1 "").splitOn
                  ("AUDIT-REGION" ++ "-END") |>.headD ""
  let n (t : String) : Nat := (region.splitOn t).length - 1          -- occurrences of `t`
  match n ("[" ++ " " ++ "]"), n ("[" ++ "!" ++ "]") with            -- unaudited [ ], flagged [!]
  | 0, 0 => logInfo "audit gate: all items audited ✓"
  | a, b => logError s!"AUDIT INCOMPLETE: {a} unaudited [ ] + {b} flagged [!] still open"
