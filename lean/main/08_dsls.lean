/-
## 通过繁饰嵌入 DSL

在本章中，我们将学习如何通过繁饰（elaboration）来构建一个领域特定语言（DSL）。我们不会全面探索 `MetaM` 的全部功能，而是简单地演示如何访问这个底层机制。

更具体地说，我们将使 Lean 理解 [IMP](http://concrete-semantics.org/concrete-semantics.pdf) 的语法。IMP 是一个简单的命令式语言，通常用于教学操作和指称语义。

我们不会完全按照书中的编码方式来定义所有内容。比如，书中定义了算术表达式和布尔表达式。而我们将走一条不同的路径，只定义接受一元或二元运算符的通用表达式。

这意味着我们将允许出现像 `1 + true` 这样的奇怪表达式！不过这会简化编码、语法以及元编程的教学过程。

### 定义抽象语法树（AST）

我们首先定义我们的原子字面量：
-/

import Lean

open Lean Elab Meta

inductive IMPLit
  | nat  : Nat  → IMPLit
  | bool : Bool → IMPLit

/- 这是我们唯一的一个一元运算符： -/
inductive IMPUnOp
  | not

/- 接下来是我们的二元运算符： -/

inductive IMPBinOp
  | and | add | less

/- 现在我们定义我们要处理的表达式： -/

inductive IMPExpr
  | lit : IMPLit → IMPExpr
  | var : String → IMPExpr
  | un  : IMPUnOp → IMPExpr → IMPExpr
  | bin : IMPBinOp → IMPExpr → IMPExpr → IMPExpr

/-
最后，我们定义语言中的命令。我们遵循书中的结构，表示「程序的每个部分也是一个程序」：
-/

inductive IMPProgram
  | Skip   : IMPProgram
  | Assign : String → IMPExpr → IMPProgram
  | Seq    : IMPProgram → IMPProgram → IMPProgram
  | If     : IMPExpr → IMPProgram → IMPProgram → IMPProgram
  | While  : IMPExpr → IMPProgram → IMPProgram

/-
### 繁饰字面量

现在我们已经定义了数据类型，接下来我们将 `Syntax` 转换为 `Expr` 类型的项。我们从定义字面量的语法和繁饰函数开始。
-/

declare_syntax_cat imp_lit
syntax num       : imp_lit
syntax "true"    : imp_lit
syntax "false"   : imp_lit

def elabIMPLit : Syntax → MetaM Expr
  -- `mkAppM` 由给定函数 `Name` 和参数，创建一个 `Expr.app`，
  -- `mkNatLit` 由一个 `Nat` 创建一个 `Expr`
  | `(imp_lit| $n:num) => mkAppM ``IMPLit.nat  #[mkNatLit n.getNat]
  | `(imp_lit| true  ) => mkAppM ``IMPLit.bool #[.const ``Bool.true []]
  | `(imp_lit| false ) => mkAppM ``IMPLit.bool #[.const ``Bool.false []]
  | _ => throwUnsupportedSyntax

elab "test_elabIMPLit " l:imp_lit : term => elabIMPLit l

#reduce test_elabIMPLit 4     -- IMPLit.nat 4
#reduce test_elabIMPLit true  -- IMPLit.bool true
#reduce test_elabIMPLit false -- IMPLit.bool true

/-
### 繁饰表达式

为了繁饰表达式，我们还需要繁饰一元和二元运算符：

请注意，这些实际上可以是纯函数（`Syntax → Expr`），但我们选择在 `MetaM` 中处理，因为这样可以更方便地抛出匹配完成的错误。
-/

declare_syntax_cat imp_unop
syntax "not"     : imp_unop

def elabIMPUnOp : Syntax → MetaM Expr
  | `(imp_unop| not) => return .const ``IMPUnOp.not []
  | _ => throwUnsupportedSyntax

declare_syntax_cat imp_binop
syntax "+"       : imp_binop
syntax "and"     : imp_binop
syntax "<"       : imp_binop

def elabIMPBinOp : Syntax → MetaM Expr
  | `(imp_binop| +)   => return .const ``IMPBinOp.add []
  | `(imp_binop| and) => return .const ``IMPBinOp.and []
  | `(imp_binop| <)   => return .const ``IMPBinOp.less []
  | _ => throwUnsupportedSyntax

/-现在我们定义表达式的语法：-/

declare_syntax_cat                   imp_expr
syntax imp_lit                     : imp_expr
syntax ident                       : imp_expr
syntax imp_unop imp_expr           : imp_expr
syntax imp_expr imp_binop imp_expr : imp_expr

/-我们还允许括号表示解析的优先级：-/

syntax "(" imp_expr ")" : imp_expr

/-
最后，我们定义递归繁饰表达式的函数：注意，表达式可以是递归的。这意味着我们的 `elabIMPExpr` 函数需要是递归的！我们需要使用 `partial`，因为 Lean 不能仅凭 `Syntax` 的消耗来证明终止性。
-/

partial def elabIMPExpr : Syntax → MetaM Expr
  | `(imp_expr| $l:imp_lit) => do
    let l ← elabIMPLit l
    mkAppM ``IMPExpr.lit #[l]
  -- `mkStrLit` 由一个 `String` 创建一个 `Expr`
  | `(imp_expr| $i:ident) => mkAppM ``IMPExpr.var #[mkStrLit i.getId.toString]
  | `(imp_expr| $b:imp_unop $e:imp_expr) => do
    let b ← elabIMPUnOp b
    let e ← elabIMPExpr e -- 递归!
    mkAppM ``IMPExpr.un #[b, e]
  | `(imp_expr| $l:imp_expr $b:imp_binop $r:imp_expr) => do
    let l ← elabIMPExpr l -- 递归!
    let r ← elabIMPExpr r -- 递归!
    let b ← elabIMPBinOp b
    mkAppM ``IMPExpr.bin #[b, l, r]
  | `(imp_expr| ($e:imp_expr)) => elabIMPExpr e
  | _ => throwUnsupportedSyntax

elab "test_elabIMPExpr " e:imp_expr : term => elabIMPExpr e

#reduce test_elabIMPExpr a
-- IMPExpr.var "a"

#reduce test_elabIMPExpr a + 5
-- IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.nat 5))

#reduce test_elabIMPExpr 1 + true
-- IMPExpr.bin IMPBinOp.add (IMPExpr.lit (IMPLit.nat 1)) (IMPExpr.lit (IMPLit.bool true))

/-
### 繁饰程序

现在我们有了繁饰 IMP 程序所需的一切！
-/

declare_syntax_cat           imp_program
syntax "skip"              : imp_program
syntax ident ":=" imp_expr : imp_program

syntax imp_program ";;" imp_program : imp_program

syntax "if" imp_expr "then" imp_program "else" imp_program "fi" : imp_program
syntax "while" imp_expr "do" imp_program "od" : imp_program

partial def elabIMPProgram : Syntax → MetaM Expr
  | `(imp_program| skip) => return .const ``IMPProgram.Skip []
  | `(imp_program| $i:ident := $e:imp_expr) => do
    let i : Expr := mkStrLit i.getId.toString
    let e ← elabIMPExpr e
    mkAppM ``IMPProgram.Assign #[i, e]
  | `(imp_program| $p₁:imp_program ;; $p₂:imp_program) => do
    let p₁ ← elabIMPProgram p₁
    let p₂ ← elabIMPProgram p₂
    mkAppM ``IMPProgram.Seq #[p₁, p₂]
  | `(imp_program| if $e:imp_expr then $pT:imp_program else $pF:imp_program fi) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    let pF ← elabIMPProgram pF
    mkAppM ``IMPProgram.If #[e, pT, pF]
  | `(imp_program| while $e:imp_expr do $pT:imp_program od) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    mkAppM ``IMPProgram.While #[e, pT]
  | _ => throwUnsupportedSyntax

/-
然后我们就可以测试完整的繁饰流程了。遵循以下语法：
-/

elab ">>" p:imp_program "<<" : term => elabIMPProgram p

#reduce >>
a := 5;;
if not a and 3 < 4 then
  c := 5
else
  a := a + 1
fi;;
b := 10
<<
-- IMPProgram.Seq (IMPProgram.Assign "a" (IMPExpr.lit (IMPLit.nat 5)))
--   (IMPProgram.Seq
--     (IMPProgram.If
--       (IMPExpr.un IMPUnOp.not
--         (IMPExpr.bin IMPBinOp.and (IMPExpr.var "a")
--           (IMPExpr.bin IMPBinOp.less (IMPExpr.lit (IMPLit.nat 3)) (IMPExpr.lit (IMPLit.nat 4)))))
--       (IMPProgram.Assign "c" (IMPExpr.lit (IMPLit.nat 5)))
--       (IMPProgram.Assign "a" (IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.nat 1)))))
--     (IMPProgram.Assign "b" (IMPExpr.lit (IMPLit.nat 10))))
