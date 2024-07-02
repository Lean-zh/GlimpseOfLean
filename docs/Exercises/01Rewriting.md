```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Data.Complex.Exponential
open Real
```

# 计算

## 环算策略

在学习数学的过程中，我们遇到的最早的一种证明是通过计算来证明。这可能听起来不像是一种证明，但实际上这是在使用表达数字运算性质的引理。当然，我们通常不想显式地调用这些，所以 mathlib 有一个 `ring` 策略，专门处理通过应用所有交换环的性质而得出的等式证明。

```lean
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
}
```

现在轮到你了，将下面的 "sorry" 替换为一个证据。在这个例子中，证明只是 `ring`。
在你证明一些事情之后，你会看到一个小的 "No goals" 消息，这是你的证明已经完成的标志。

```lean
example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by {
  sorry
}
```

在上述的第一个例子中，认真思考 Lean 在哪里显示括号。
`ring` 策略当然知道乘法的结合律，但理解二元操作真的是二元的以及类似
`a*b*c` 的表达式被 Lean 读作 `(a*b)*c` ，这是有帮助的。事实上这等于 `a*(b*c)` 是一个引理
当需要时会被 `ring` 策略使用。

## 重写策略

让我们现在看看如何利用涉及数字的假设进行计算。
这利用了等式的基本属性：如果两个数学对象 A 和 B 是相等的，那么在任何涉及 A 的陈述中，都可以用 B 来代替 A。这个操作被称为重写，而 Lean 的策略对应的命名为 `rw`。请仔细逐步理解下面的证明，并尝试理解正在发生的事情。

```lean
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h]
  rw [h']
  ring
}
```

注意 `rw` 策略是用来改变当前目标的。在上述证明的第一行之后，新的目标是 `b + c + e = d + c`。因此，你可以把这第一步证明理解为："我想要证明，`a + e = d + c`，但是，由于假设 `h` 告诉我 `a = b + c`，我只需要证明 `b + c + e = d + c` 就足够了。"

实际上，我们可以在一条命令中做几个重写。

```lean
example (a b c d : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h, h']
  ring
}
```

注意，将光标置于 `h` 和 `h'` 之间会显示中间的证明状态。

还需要注意的是，策略状态背景色的细微变化，绿色部分表示新的内容，红色部分表示即将改变的部分。

现在请你自己试试。注意 `ring` 依然可以进行计算，但它并不使用假设 `h` 和 `h'`。

```lean
example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by {
  sorry
}
```

## 使用引理进行重写

在前面的示例中，我们使用本地假设重写了目标。但我们也可以使用引理。例如，让我们证明一个关于指数的引理。
由于 `ring` 只知道如何从环的公理中证明事物，它不知道如何处理指数。
对于以下的引理，我们将两次使用引理 `exp_add x y` 进行重写，该引理证明了 `exp(x+y) = exp(x) * exp(y)`。

```lean
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add (a + b) c]
  rw [exp_add a b]
}
```

请注意，在第二次 `rw` 之后，目标变为
`exp a * exp b * exp c = exp a * exp b * exp c`，Lean 会立即声明证明已经完成。

如果我们不提供引理的参数，Lean 将重写第一个匹配的子表达式。在我们的示例中，这已经足够好。有时需要更多的控制。

```lean
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add, exp_add]
}
```

让我们做一个练习，你也需要使用
`exp_sub x y : exp(x-y) = exp(x) / exp(y)` 和 `exp_zero : exp 0 = 1`。

记住，`a + b - c` 代表的是 `(a + b) - c`。

你可以使用 `ring` 或者通过重写 `mul_one x : x * 1 = x` 来简化等式右侧的分母。

```lean
example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by {
  sorry
}
```

## 从右至左进行重写

由于等式是对称的，我们也可以使用 `←` ，将等式的右边替换为左边，如下例所示。

```lean
example (a b c : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by {
  rw [← h, h']
}
```

无论何时，只要你在 Lean 文件中看到你键盘上没有的符号，比如 ←，你都可以将鼠标光标放在其上方，通过工具提示学习如何输入它。对于 ← 这个符号，你可以通过输入 "\l "，也就是反斜杠-l-空格来输入。

注意，这种从右到左的重写都是关心你想要*使用*的等式的两边，而不是你想要*证明*的东西的两边。`rw [← h]` 将会用左边替换右边，因此它会在当前目标中寻找 `b + c` 并将其替换为 `a`。

```lean
example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by {
  sorry
}
```

## 在局部假设中重写

我们也可以在局部上下文的假设中进行重写，例如使用
  `rw [exp_add x y] at h`
来替换假设 `h` 中的 `exp(x + y)` 为 `exp(x) * exp(y)`。

`exact` 策略允许你给出显式的证明项来证明当前的目标。

```lean
example (a b c d : ℝ) (h : c = d*a - b) (h' : b = a*d) : c = 0 := by {
  rw [h'] at h
  ring at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h
}
```

## 使用 calc 进行计算布局

上述例子所写的内容与我们在纸上写的内容相去甚远。让我们看看如何获得更自然的布局（同时也恢复使用 `ring` 而不是显式的引理调用）。
在下面的每个 `:=` 之后，目标是证明与前面一行（或第一行的左边）相等。
通过将鼠标指针置于每个 `by` 后面并查看策略状态，仔细检查你是否理解了这一点。

```lean
example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by {
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring
}
```

我们来使用 `calc` 做一些练习。

```lean
example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by {
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by sorry
              _ = exp ((b + b) + (c + c))           := by sorry
              _ = exp (b + b) * exp (c + c)         := by sorry
              _ = (exp b * exp b) * (exp c * exp c) := by sorry
              _ = (exp b) ^ 2 * (exp c)^2           := by sorry
}
```

从实际角度来看，在编写这样的证明时，有时候采取以下操作会很方便：
* 通过在 Lean 信息视图面板的右上角点击暂停图标按钮，暂停 VScode 中的策略状态视图更新。
* 编写完整的计算过程，每行结束时用“:= ?_”。
* 通过点击播放图标按钮恢复策略状态更新，并填充证明。

下划线应放在 `calc` 下面的第一行的左手边的部分下面。
将等号和 `:= `  对齐并不是必要的，但会显得整洁。

```lean
example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by {
  sorry
}
```

恭喜你，这是你的第一个练习文件的结束！你已经看到了 Lean 证明的格式以及学习了以下策略：
* `ring`
* `rw`
* `exact`
* `calc`
