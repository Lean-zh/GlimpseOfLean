```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Data.Complex.Exponential
open Real
```

# 计算

## 环策略

在学习数学时，我们遇到的最早的证明之一是通过计算进行证明。这可能听起来不像是一个证明，但实际上这是使用表达数字运算性质的引理。当然，我们通常不想显式地调用这些引理，因此 mathlib 提供了一个叫做 `ring` 的策略，用于证明遵循所有交换环运算性质的等式。

```lean
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
}
```

现在轮到你了，请将下方的 `sorry` 替换为一个证明。在这种情况下，证明只需使用 `ring`。

```lean
example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by {
  -- sorry
  ring
  -- sorry
}
```

在上面的第一个例子中，请仔细观察 Lean 显示括号的位置。`ring` 策略当然知道乘法的结合性，但有时理解二元运算的二元性以及类似 `a*b*c` 的表达式在 Lean 中被解析为 `(a*b)*c`，而它等于 `a*(b*c)` 是一个引理，当需要时 `ring` 策略会使用这个引理。

## 重写策略

现在让我们看看如何利用与所涉及的数字相关的假设进行计算。这使用了等式的基本属性：如果两个数学对象 A 和 B 相等，那么在涉及到 A 的任何陈述中，我们可以用 B 替换 A。这个操作称为重写，而 Lean 中的策略是 `rw`。仔细逐步执行下方的证明，并试着理解正在发生的事情。

```lean
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h]
  rw [h']
  ring
}
```

注意，`rw` 策略会改变当前目标。在上面证明的第一行之后，新的目标是 `b + c + e = d + c`。因此，你可以将这个第一步证明解读为说："我想证明 `a + e = d + c`，但是由于假设 `h` 告诉我 `a = b + c`，我可以用 `h` 来替换 `a`，
实际上，我们可以一次进行多次重写。

```lean
example (a b c d : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h, h']
  ring
}
```

注意，在 `h` 和 `h'` 之间放置光标，可以显示中间的证明状态。

还要注意策略状态中微妙的背景色变化，显示了新内容是绿色的，即将改变的内容是红色的。

现在请你自己尝试一下。注意，`ring` 仍然可以进行计算，但它不使用假设 `h` 和 `h'`。

```lean
example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by {
  -- sorry
  rw [h', h]
  ring
  -- sorry
}
```

## 使用引理进行重写

在前面的例子中，我们使用局部假设进行了重写。但我们也可以使用引理。例如，让我们证明一个关于指数运算的引理。由于 `ring` 仅知道如何从环的公理证明事实，它不知道如何处理指数运算。对于以下引理，我们将使用引理 `exp_add x y` 两次进行重写，该引理证明了 `exp(x+y) = exp(x) * exp(y)`。

```lean
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add (a + b) c]
  rw [exp_add a b]
}
```

还要注意，在第二次 `rw` 之后，目标变为 `exp a * exp b * exp c = exp a * exp b * exp c`，Lean 立即声明证明完成。

如果我们不为引理提供参数，Lean 将重写第一个匹配的子表达式。在我们的例子中，这已经足够了。但有时可能需要更多的控制。

```lean
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add, exp_add]
}
```

让我们做一个练习，你还需要使用 `exp_sub x y: exp(x-y) = exp(x) / exp(y)` 和 `exp_zero: exp 0 = 1`。

请记住，`a + b - c` 表示 `(a + b) - c`。

你可以使用 `ring` 或重写策略 `mul_one x: x * 1 = x` 来简化分母。
在右边。

```lean
example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by {
  -- sorry
  rw [exp_sub, exp_add, exp_zero, mul_one]
  -- sorry
}
```

## 反向重写

由于等号是对称关系，我们也可以使用 `←` 将等式的右边替换为左边，如下面的例子所示。

```lean
example (a b c : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by {
  rw [← h, h']
}
```

无论何时在 Lean 文件中看到一个你在键盘上看不到的符号，比如 `←`，你可以将鼠标光标移动到其上方，从工具提示中了解如何输入它。在 `←` 的情况下，你可以通过输入 "\l " 来输入它，即反斜杠-l-空格。

需要注意的是，这种从右到左的重写故事只涉及你想要*使用*的等式的两边，而不是你想要*证明*的两边。`rw [← h]` 会将右边替换为左边，因此它将在当前目标中查找 `b + c`，并将其替换为 `a`。

```lean
example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by {
  -- sorry
  rw [← h', ← h, ← h'']
  -- sorry
}
```

## 在局部假设中进行重写

我们还可以在局部上下文中的假设进行重写，例如使用以下形式的重写策略：
`rw [exp_add x y] at h`
这样可以在假设 `h` 中用 `exp(x + y)` 替换为 `exp(x) * exp(y)`。

`exact` 策略允许你为当前目标提供一个显式的证明项来证明它。

```lean
example (a b c d : ℝ) (h : c = d*a - b) (h' : b = a*d) : c = 0 := by {
  rw [h'] at h
  ring at h
  -- 我们的假设 `h` 现在正好是我们要证明的内容
  exact h
}
```

## 使用 calc 进行计算

上面例子中的写法与我们在纸上写的写法非常不同。现在让我们看看如何获得更自然的布局（并返回使用 `ring` 而不是显式引理调用的方式）。
在下面每个 `:=` 后面，目标是证明与前一行相等的内容。
（或第一行中的左边）。
逐行检查，将光标放在每个 `by` 后面，并查看策略状态来确保你理解了这一点。

```lean
example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by {
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring
}
```

让我们用 `calc` 来做一些练习。

```lean
example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by {
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by rw [h]
              _ = exp ((b + b) + (c + c))           := by ring
              _ = exp (b + b) * exp (c + c)         := by rw [exp_add]
              _ = (exp b * exp b) * (exp c * exp c) := by rw [exp_add, exp_add]
              _ = (exp b) ^ 2 * (exp c)^2           := by ring
}
```

从实际角度来看，当编写这样的证明时，有时候可以：
* 在 VSCode 中通过点击 Lean Infoview 面板右上角的暂停图标按钮来暂停策略状态视图的更新。
* 写下完整的计算，每行以 ":= ?_" 结束。
* 点击播放图标按钮恢复策略状态更新，并填写证明。

下划线应该放在第一行下面的左边。将等号和 `:=` 对齐不是必需的，但看起来整洁。

```lean
example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by {
  -- sorry
  calc
    c = d*a + b   := by rw [h]
    _ = d*a + a*d := by rw [h']
    _ = 2*a*d     := by ring
  -- sorry
}
```

恭喜！你已完成第一个练习文件！你已经看到了 Lean 证明的输入方式，并学习了以下策略：
* `ring`
* `rw`
* `exact`
* `calc`
