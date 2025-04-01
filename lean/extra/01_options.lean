/-
# 额外内容：选项

选项（Option）是一种向元程序和 Lean 编译器传达一些特殊配置的方法。基本上它只是一个 [`KVMap`](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/KVMap.lean)，这是一个从 `Name` 到 `Lean.DataValue` 的简单映射。目前有 6 种数据值：
- `String`
- `Bool`
- `Name`
- `Nat`
- `Int`
- `Syntax`

通过 `set_option` 命令设置一个选项，告诉 Lean 编译器对程序做一些不同的处理是非常简单的：
-/

import Lean
open Lean

#check 1 + 1 -- 1 + 1 : Nat

set_option pp.explicit true -- 在美观打印中不使用通常的语法

#check 1 + 1 -- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1 1 : Nat

set_option pp.explicit false

/-!
你还可以将选项值限制为仅适用于下一个命令或表达式：
-/

set_option pp.explicit true in
#check 1 + 1 -- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1 1 : Nat

#check 1 + 1 -- 1 + 1 : Nat

#check set_option trace.Meta.synthInstance true in 1 + 1 -- 显示类型类合成 `OfNat` 和 `HAdd` 的途径

/-!
如果你想知道目前有哪些选项可用，你可以直接码出 `set_option` 空一格然后编辑器会自动弹出代码建议。在调试某些元程序时，最有用的一类选项是 `trace.`。

## 元编程中的选项
现在我们已经知道如何设置选项了，接下来我们来看一下元程序如何访问这些选项。最常见的方法是通过 `MonadOptions` 类型类，这个类扩展了 `Monad`，提供了一个函数 `getOptions : m Options`。目前，它在以下类型中得到了实现：
- `CoreM`
- `CommandElabM`
- `LevelElabM`
- 所有可以提升上述某个类型操作的 monad（例如 `MetaM` 是从 `CoreM` 提升的）

一旦我们有了 `Options` 对象，我们就可以通过 `Option.get` 查询相关信息。
为了演示这一点，让我们编写一个命令来打印 `pp.explicit` 的值。
-/

elab "#getPPExplicit" : command => do
  let opts ← getOptions
  logInfo s!"pp.explicit : {pp.explicit.get opts}"

#getPPExplicit -- pp.explicit : false

set_option pp.explicit true in
#getPPExplicit -- pp.explicit : true

/-!
注意到，获取 `pp.explicit` 的实际实现 `Lean.getPPExplicit` 使用了 `pp.all` 是否被设置作为默认值。

## 自定义选项
声明我们自己的选项也非常简单。Lean 编译器提供了一个宏 `register_option` 来实现这一功能。让我们来看一下它的用法：
-/

register_option book.myGreeting : String := {
  defValue := "Hello World"
  group := "pp"
  descr := "just a friendly greeting"
}

/-!
然而，我们不能在声明选项的同一个文件中直接使用它，因为有初始化的限制。
-/
