/-
# 语法

本章主要讨论在 Lean 中声明和操作语法的方法。由于操作语法的方式有很多种，我们不会在这里深入探讨，而是将相当一部分内容留到后续章节。

## 声明语法

### 声明辅助工具

有些读者可能熟悉 `infix` 或者 `notation` 命令，对于不熟悉的读者，以下是简要回顾：
-/

import Lean

-- XOR, 输入 \oplus
infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- 使用`notation`, "左XOR"
notation:10 l:10 " LXOR " r:11 => (!l && r)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-
`infixl` 命令声明一个左结合中缀二元运算符。此外 `prefix` 表示前缀。末尾的`l`表示左，对应地 `infixr` 意味着右结合。`=>`右侧表示符号所对应的二元函数。

`notation` 命令更自由：我们可以直接在语法定义中「提到」参数，并在右侧对它们进行操作。更棒的是，理论上我们可以通过 `notation` 命令创建从 0 到任意多个参数的语法，因此它也常被称为「mixfix」表示法。

留意：
- 我们在运算符周围留有空格：" ⊕ "，" LXOR "。这样做是为了当 Lean 以后漂亮打印我们的语法时，它也会在运算符周围使用空格，否则语法会显示为 `l⊕r`，而不是 `l ⊕ r`。

命令之后的 `60` 和 `10` -- 这些表示运算符的优先级，意思是它们与参数绑定的强度，让我们来看看它的实际效果：
-/

#eval true ⊕ false LXOR false -- false 这说明 ⊕ 符号的优先级比 LXOR 更高（60 > 10）
#eval (true ⊕ false) LXOR false -- false
#eval true ⊕ (false LXOR false) -- true

/-!
`notation:precedence` 的用法更能反映优先级具体实现的机制。例如：
-/

#eval true LXOR false LXOR true -- true 这说明它也是左结合的
#eval (true LXOR false) LXOR true -- true
#eval true LXOR (false LXOR true) -- false

/-!
`notation:10` 代表 `a LXOR b` 一整块的优先级为10，也就是说可以看作 `(a LXOR b):10 LXOR c`。`l:10` 和 `r:11` 意为左侧参数的优先级必须**至少**为10，而右侧参数的优先级必须**至少**为11。这样就杜绝了右结合的可能，因为 `a LXOR (b LXOR c):10` 不满足 `r:11`。想要定义一个右结合符号，可以这样做：
-/

notation:10 l:11 " LXORr " r:10 => (!l && r)
#eval true LXORr false LXORr true -- false

/-!

注意：如果符号没有显式指定优先级，它们会默认被赋予优先级0。

本节的最后一点说明：只要优先级允许, Lean 总是试图获得最长的匹配解析，这有三个重要的影响。首先，一个非常直观的例子，如果我们有一个右结合运算符 `^`，Lean 看到类似 `a ^ b ^ c` 的表达式时，它会首先解析 `a ^ b` 成功，然后是 `(a ^ b) ^ c` 失败，最终解析为 `a ^ (b ^ c)` 成功。

其次，如果我们有一个符号，其优先级不足以确定表达式应如何加括号，例如：
-/

notation:65 lhs:65 " ~ " rhs:65 => (lhs - rhs)

/-
像 `a ~ b ~ c` 这样的表达式将被解析为 `a ~ (b ~ c)`，因为 Lean 试图找到最长的解析方式。作为一条经验法则：如果优先级不明确，Lean 会默认为右结合。
-/

#eval 5 ~ 3 ~ 3 -- 结果为 5，因为这被解析为 5 - (3 - 3)

/-
最后，如果我们定义了重叠的符号，例如：
-/

-- 定义 `a ~ b mod rel` 表示 a 和 b 在某种等价关系 rel 下是等价的
notation:65 a:65 " ~ " b:65 " mod " rel:65 => rel a b

/-
Lean 会优先选择这种符号，而不是先解析为上面定义的 `a ~ b`，然后因为不知道如何处理 `mod` 和等价关系参数而报错。
-/

#check 0 ~ 0 mod Eq -- 0 = 0 : Prop

/-
这也是因为 Lean 正在寻找最长的解析方式，在这种情况下，还包括了 `mod` 和等价关系参数。
-/

/-
### 自由形式的语法声明
通过上面的 `infix` 和 `notation` 命令，你已经可以声明相当丰富的普通数学语法了。然而，Lean 也允许你引入任意复杂的语法。这是通过两个主要命令 `syntax` 和 `declare_syntax_cat` 实现的。`syntax` 命令允许你为已经存在的「语法类别」添加一个新的语法规则。最常见的语法类别有：
- `term`，这个类别将在繁饰章节中详细讨论，目前你可以将其理解为「任何可求值的东西」
- `command`，这是用于顶级命令的类别，如 `#check`、`def` 等。
- TODO: ...

让我们来看看它的实际效果：
-/

syntax "MyTerm" : term

/-
现在我们可以用 `MyTerm` 替代诸如 `1 + 1` 这样的表达式，它在语法上是有效的，但这并不意味着代码可以编译成功，这只是表示 Lean 解析器可以理解它：
-/

#check_failure MyTerm
-- elaboration function for 'termMyTerm' has not been implemented  MyTerm
-- 尚未实现 'termMyTerm' 的繁饰函数

/- 注意：`#check_failure` 命令允许以不报错的方式标记类型错误的表达式。 -/

/-
繁饰函数，即将这种语法转换为 `Expr` 类型，是繁饰章节的主题。

`notation` 和 `infix` 命令是一种方便的工具，将语法声明与宏定义捆绑在一起（关于宏的更多内容，请参见宏章节），其中 `=>` 左侧的内容声明了语法。
之前提到的关于优先级的所有原则同样适用于 `syntax`。

当然，我们也可以在自己的声明中涉及其他语法，以构建语法树。例如，我们可以尝试构建一个简单的布尔表达式语言：
-/

namespace Playground2

-- `scoped` 修饰符确保语法声明仅在该 `namespace` 中有效，以便我们在本章中不断修改它
scoped syntax "⊥" : term -- ⊥ 表示 false
scoped syntax "⊤" : term -- ⊤ 表示 true
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
#check_failure ⊥ OR (⊤ AND ⊥) -- 繁饰函数尚未实现，但解析通过

end Playground2

/-
当下 `AND` 和 `OR` 操作的左右侧可以使用任意的 `term`。如果我们希望限制操作的「定义域」，例如仅接受（我们当下定义的）布尔表达式，我们将需要额外声明自己的语法类别。这可以通过 `declare_syntax_cat` 命令实现：
-/

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

/-
现在我们正在使用自己的语法类别，已经完全与系统的其他部分断开连接。这些不再是 `term` 了：

```lean
#check ⊥ AND ⊤ -- 期望是 `term`
```
但我们希望 `boolean_expr` 仍是 `term` 的一部分，除非你想重新从头开始写一切。实际上通常我们需要使用新的语法扩展已有的语法类别。也就是把 `boolean_expr` 重新嵌入到 `term` 类别中：
-/

syntax "[Bool|" boolean_expr "]" : term
#check_failure [Bool| ⊥ AND ⊤] -- 繁饰函数尚未实现，但解析通过

/-
### 语法组合器
更复杂的语法通常需要系统内置一些基本的语法操作，包括：

- 无语法类别的辅助解析器（即不可扩展）
- 选择（A或B）
- 重复（AAAAAA……）
- 可选项（可有可无）

虽然所有这些操作都可以通过语法类别进行编码，但有时会显得非常冗杂，因此 Lean 提供了更简便的方式来实现这些操作。

为了展示这些操作的实际效果，我们将简要定义一个简单的二进制表达式语法。

**无语法类别**

首先，声明不属于任何语法类别的命名解析器与普通的 `def` 非常相似：
-/

syntax binOne := "O"
syntax binZero := "Z"

/-
这些命名解析器可以像上面的语法类别一样在相同位置使用，唯一的区别是它们不可扩展。
即它们在语法声明中直接展开，而我们不能像定义语法类别那样为它们定义新的模式。
此外，Lean 内置了一些非常有用的命名解析器，最著名的是：
- `str` 表示字符串字面量
- `num` 表示数字字面量
- `ident` 表示标识符
- … TODO: 完善列表或链接到编译器文档

**选择**

接下来，我们希望声明一个能够理解数字的解析器，二进制数字要么是 0 要么是 1，因此我们可以这样写：
-/

syntax binDigit := binZero <|> binOne

/-
其中 `<|>` 运算符实现了「接受左侧或右侧」的行为。我们还可以将它们链式组合，以实现能够接受任意多个复杂解析器的组合。

**重复**

现在，我们将定义二进制数的概念，通常二进制数会直接写作一串数字，但为了展示重复特性，我们将使用逗号分隔的方式：
-/

-- "+" 表示「一个或多个」，为了表示「零个或多个」，可以使用 "*"
-- "," 表示 `binDigit` 之间的分隔符，如果省略，则默认分隔符为一个空格
syntax binNumber := binDigit,+

/-
由于我们可以将命名解析器用于语法类别，我们现在可以轻松地将其添加到 `term` 类别：

```lean
syntax "bin(" binNumber ")" : term
#check bin(Z, O, Z, Z, O) -- 繁饰函数尚未实现，但解析通过
#check bin() -- 解析失败，因为 `binNumber` 是「一个或多个」：期望 'O' 或 'Z'
```
-/

syntax binNumber' := binDigit,* -- 注意 *
syntax "emptyBin(" binNumber' ")" : term
#check_failure emptyBin() -- 繁饰函数尚未实现，但解析通过

/-
注意，我们并不限于每个解析器只能使用一个语法组合器，我们也可以一次性编写所有内容：
-/

syntax "binCompact(" ("Z" <|> "O"),+ ")" : term --使用括号来组合
#check_failure binCompact(Z, O, Z, Z, O) -- 繁饰函数尚未实现，但解析通过

/-
**可选项**

作为最后一个功能，让我们添加一个可选填的字符串注释，用来解释所声明的二进制字面量：
-/

-- (...)? 表示括号中的部分是可有可无的
syntax "binDoc(" (str ";")? binNumber ")" : term
#check_failure binDoc(Z, O, Z, Z, O) -- 繁饰函数尚未实现，但解析通过
#check_failure binDoc("mycomment"; Z, O, Z, Z, O) -- 繁饰函数尚未实现，但解析通过

/-!
## 操作语法
如前所述，本章不会详细讨论如何教 Lean 赋予语法特定含义。不过，我们将探讨如何编写操作语法的函数。像 Lean 中的所有事物一样，语法由归纳类型 `Lean.Syntax` 表示，我们可以对其进行操作。虽然它包含了很多信息，但我们感兴趣的大部分内容可以简化为：
-/

namespace Playground2

inductive Syntax where
  | missing : Syntax
  | node (kind : Lean.SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom : String -> Syntax
  | ident : Lean.Name -> Syntax

end Playground2

/-!
我们逐个解释构造器：
- `missing` 用于表示 Lean 编译器无法解析的内容，这使得 Lean 能在文件的某个部分存在语法错误时，仍能从错误中恢复并继续解析其他部分。基本上，我们对这个构造器不太关心。
- `node`，顾名思义，是语法树中的一个节点。它有一个所谓的 `kind : SyntaxNodeKind`，其中 `SyntaxNodeKind` 就是一个 `Lean.Name`。基本上，每个 `syntax` 声明都会自动生成一个 `SyntaxNodeKind`（我们也可以通过 `syntax (name := foo) ... : cat` 明确指定名称），这样我们可以告诉 Lean「这个函数负责处理这个特定的语法构造」。此外，像所有树中的节点一样，它有子节点，在这种情况下是 `Array Syntax`。
- `atom` 表示语法层次结构中除一个例外的所有对象。例如，我们之前的操作符 ` ⊕ ` 和 ` LXOR ` 将被表示为 atom。
- `ident` 是前述规则的例外。`ident` 和 `atom` 的区别也很明显：标识符有一个 `Lean.Name` 而不是表示它的 `String`。为什么 `Lean.Name` 不是 `String` 这一点与一个叫做宏卫生的概念有关，我们将在宏章节中详细讨论。现在可以把它们看作基本等价。

### 构造新的 `Syntax`
现在我们知道了 Lean 中语法的表示方法，当然可以编写生成这些归纳树的程序，然而这样做会非常繁琐，显然不是我们想要的。幸运的是，Lean 中有相当大量的API隐藏在 `Lean.Syntax` 命名空间中，可以供我们探索：
-/

open Lean
#check Syntax -- Syntax. autocomplete

/-!
用于创建 `Syntax` 的有趣函数是那些以 `Syntax.mk*` 开头的函数，它们允许我们创建非常基础的 `Syntax` 对象，如 `ident`，也可以创建更复杂的对象，比如 `Syntax.mkApp`，我们可以用它来创建 `Syntax` 对象，相当于将第一个参数中的函数应用于第二个参数中的参数列表（所有都作为 `Syntax` 传递）。让我们看一些例子：
-/

-- 名字字面量使用反引号 ` 表示
#eval Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"] -- 这是 `Nat.add 1 1` 的语法
#eval mkNode `«term_+_» #[Syntax.mkNumLit "1", mkAtom "+", Syntax.mkNumLit "1"] -- 这是 `1 + 1` 的语法

-- 注意 `«term_+_»` 是自动生成的用于加法语法的 SyntaxNodeKind

/-!
大家都不喜欢这种创建 `Syntax` 的方式。然而，这样做涉及一些机器的工作，尤其是为了让它漂亮且正确（大部分是为了正确）。这些内容将在宏章节中详细解释。

### `Syntax` 中的匹配
正如构造 `Syntax` 是一个重要主题，特别是对于宏而言，匹配语法同样（甚至更）有趣。幸运的是，我们不必直接在归纳类型本身上进行匹配：相反，我们可以使用所谓的「语法模式」。它们非常简单，其语法就是 `` `(我想匹配的语法) ``。我们来看一个例子：
-/

def isAdd11 : Syntax → Bool
  | `(Nat.add 1 1) => true
  | _ => false

#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- true
#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- false

/-!
匹配还可以从输入中捕获变量，而不仅仅是匹配字面量，这是通过一个稍微复杂一点的语法来实现的：
-/

def isAdd : Syntax → Option (Syntax × Syntax)
  | `(Nat.add $x $y) => some (x, y)
  | _ => none

#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo]) -- none

/-
### 类型化的语法
注意到这个例子中的 x 和 y 的类型是 `TSyntax term`，而不是 Syntax。虽然我们正在对 Syntax 进行模式匹配，正如我们在构造函数中所看到的，Syntax 仅由不是 TSyntax 的类型组成，那么这里发生了什么？基本上，`` `() `` 语法足够智能，能够识别我们要匹配的语法可能来自的最通用的语法类别（在这个例子中是 term）。然后它将使用参数化为该语法类别名称的类型化语法类型 TSyntax。这不仅让程序员更容易看清正在发生的事情，还带来了其他好处。例如，如果我们在下一个例子中将语法类别限制为 num，Lean 将允许我们直接在结果的 `TSyntax num` 上调用getNat，而不需要模式匹配或担心潜在错误。
-/

-- 现在我们还明确标记了函数以操作 term 语法
def isLitAdd : TSyntax `term → Option Nat
  | `(Nat.add $x:num $y:num) => some (x.getNat + y.getNat)
  | _ => none

#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some 2
#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- none

/-!
如果你想访问 `TSyntax` 背后的 `Syntax`，可以使用 `TSyntax.raw`，尽管在大多数情况下，强制转换机制应该可以正常工作。
我们将在宏章节中看到 `TSyntax` 系统的其他好处。

关于语法匹配的最后一个重要说明：在这个基本形式中，它只适用于 `term` 类别的语法。如果你想用它来匹配你自己的语法类别，就需要使用 `` `(category| ...)``。

### 项目示例
作为本章的最后一个迷你项目，我们将声明一个迷你算术表达式语言的语法以及一个类型为 `Syntax → Nat` 的函数来求值。我们将在未来的章节中看到更多关于下面介绍的一些概念。
-/

declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

-- 你可以忽略 `Elab.TermElabM`，对我们来说重要的是它允许我们使用 `` `(arith| (12 + 3) - 4) `` 符号来构造 `Syntax`，而不仅仅是能够像这样进行匹配。
def test : Elab.TermElabM Nat := do
  let stx ← `(arith| (12 + 3) - 4)
  pure (denoteArith stx)

#eval test -- 11

/-!
随意玩弄这个例子，并根据需要扩展它。接下来的章节主要会讨论以某种方式操作 `Syntax` 的函数。

## 更复杂的例子

### 使用类型类进行符号定义

我们可以使用类型类来添加通过类型而不是语法系统可扩展的符号，这正是 Lean 中 `+` 如何使用类型类 `HAdd` 和 `Add` 以及其他常见运算符被通用定义的方式。

例如，我们可能想要为子集符号定义一个通用符号。第一步是定义一个捕捉我们想要构建符号的函数的类型类。
-/

class Subset (α : Type u) where
  subset : α → α → Prop

/-!
第二步是定义符号，我们可以在这里做的就是将代码中每个出现的 `⊆` 转换为对 `Subset.subset` 的调用，因为类型类解析应该能够找出所引用的 `Subset` 实例。因此，符号很简单：
-/

-- 优先级在此示例中是任意的
infix:50 " ⊆ " => Subset.subset

/-!
让我们定义一个简单的集合论来进行测试：
-/

-- `Set` 是由其包含的元素定义的
-- 也就是对其元素类型的一个简单谓词
def Set (α : Type u) := α → Prop

def Set.mem (x : α) (X : Set α) : Prop := X x

-- 集成到已存在的成员符号类型类中
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

instance : Subset (Set α) where
  subset X Y := ∀ (x : α), x ∈ X → x ∈ Y

example : ∀ (X : Set α), Set.empty ⊆ X := by
  intro X x
  -- ⊢ x ∈ Set.empty → x ∈ X
  intro h
  exact False.elim h -- 空集没有成员

/-!
### 绑定
由于在 Lean 3 中声明使用绑定变量符号的语法曾经是一个相当不直观的事情，因此我们将简要了解在 Lean 4 中这可以多么自然地完成。

在这个例子中，我们将定义包含所有元素 `x` 的集合的著名记号 -- 满足某个属性的集合：例如 `{x ∈ ℕ | x < 10}`。

首先，我们需要稍微扩展上述集合理论：
-/

-- 基本的「所有元素满足」函数，用于该符号
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
有了这个函数，我们现在可以尝试直观地定义我们的符号的基本版本：
-/

notation "{ " x " | " p " }" => setOf (fun x => p)

#check { (x : Nat) | x ≤ 1 } -- { x | x ≤ 1 } : Set Nat

example : 1 ∈ { (y : Nat) | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { (y : Nat) | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

/-!
这个直观的符号确实会以我们预期的方式处理我们可以抛出的内容。

至于如何扩展这个符号以允许更多集合论的内容，例如 `{x ∈ X | p x}` 并省略绑定变量周围的括号，参考宏章节。

## 练习

1. 创建一个「紧急减法」符号💀，使得 `5 * 8 💀 4` 返回 `20`，而 `8 💀 6 💀 1` 返回 `3`。

    **a)** 使用 `notation` 命令。
    **b)** 使用 `infix` 命令。
    **c)** 使用 `syntax` 命令。

    提示：在 Lean 4 中，乘法定义为 `infixl:70 " * " => HMul.hMul`。

2. 考虑以下语法类别：`term`、`command`、`tactic`；以及下面给出的 3 个语法规则。利用这些新定义的语法。

    ```lean
      syntax "good morning" : term
      syntax "hello" : command
      syntax "yellow" : tactic
    ```

3. 创建一个 `syntax` 规则，可以接受以下命令：

    - `red red red 4`
    - `blue 7`
    - `blue blue blue blue blue 18`

    （所以，要么是所有的 `red` 后面跟着一个数字；要么是所有的 `blue` 后面跟着一个数字；`red blue blue 5` - 不应该有效。）

    使用以下代码模板：

    ```lean
    syntax (name := colors) ...
    -- 繁饰函数将语法注入语义
    @[command_elab colors] def elabColors : CommandElab := λ stx => Lean.logInfo "success!"
    ```

4. Mathlib 有一个 `#help option` 命令，用于显示当前环境中所有可用选项及其描述。`#help option pp.r` 将显示所有以 "pp.r" 子串开头的选项。

    创建一个 `syntax` 规则，可以接受以下命令：

    - `#better_help option`
    - `#better_help option pp.r`
    - `#better_help option some.other.name`

    使用以下模板：

    ```lean
    syntax (name := help) ...
    -- 繁饰函数将语法注入语义
    @[command_elab help] def elabHelp : CommandElab := λ stx => Lean.logInfo "success!"
    ```

5. Mathlib 有一个 ∑ 运算符。创建一个 `syntax` 规则，可以接受以下项：

    - `∑ x in { 1, 2, 3 }, x^2`
    - `∑ x in { "apple", "banana", "cherry" }, x.length`

    使用以下模板：

    ```lean
    import Std.Classes.SetNotation
    import Std.Util.ExtendedBinder
    syntax (name := bigsumin) ...
    -- 繁饰函数将语法注入语义
    @[term_elab bigsumin] def elabSum : TermElab := λ stx tp => return mkNatLit 666
    ```

    提示：使用 `Std.ExtendedBinder.extBinder` 解析器。
    提示：你需要在 Lean 项目中安装 Std4 才能使这些导入生效。
-/
