```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Data.Complex.Exponential
open Real

```

# 计算

## ring 策略

在学习数学时最早遇到的是通过计算来证明。这可能听起来不像证明，但实际上这是在使用数字运算性质的引理。当然，我们通常不想显式地调用这些引理，所以 mathlib 有一个 `ring` 策略，负责证明通过应用所有交换环的性质得出的等式。

```lean
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring

```

现在轮到你了，用证明替换下面的单词 sorry。在这种情况下，证明就是 `ring`。在你证明某些东西后，你会看到一个小的 "No goals" 消息，这表明你的证明已经完成。

```lean
example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  sorry

```

在上面的第一个例子中，仔细看看 Lean 在哪里显示括号。`ring` 策略当然知道乘法的结合律，但有时理解二元运算确实是二元的很有用，像 `a*b*c` 这样的表达式被 Lean 读作 `(a*b)*c`，而它等于 `a*(b*c)` 这个事实是 `ring` 策略在需要时使用的引理。

## 重写策略

现在让我们看看如何使用涉及相关数字的假设进行计算。这使用了等式的基本性质：如果两个数学对象 A 和 B 相等，那么在任何涉及 A 的语句中，都可以用 B 替换 A。这个操作称为重写，Lean 的基本策略是 `rw`。仔细逐步执行下面的证明，并尝试理解发生了什么。

```lean
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  rw [h']
  ring

```

注意 `rw` 策略会改变当前目标。在上面证明的第一行之后，新的目标是 `b + c + e = d + c`。所以你可以将第一个证明步骤理解为："我想要证明 `a + e = d + c`，但由于假设 `h` 告诉我 `a = b + c`，因此证明 `b + c + e = d + c`就足够了。"

`rw` 策略需要被告知每个重写步骤。稍后我们将看到更强大的策略，可以为你自动化这些繁琐的步骤。

实际上可以在一个命令中进行多次重写。

```lean
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h, h']
  ring

```

注意将光标放在 `h` 和 `h'` 之间会显示中间的证明状态。

还要注意策略状态中微妙的背景色变化，绿色显示新内容，红色显示即将改变的内容。

现在你自己试试。注意 `ring` 仍然可以进行计算，但它不使用假设 `h` 和 `h'`。

```lean
example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  sorry

```

## 使用引理进行重写

在前面的例子中，我们使用局部假设重写目标。但我们也可以使用引理。例如，让我们证明一个关于指数的引理。由于 `ring` 只知道如何从环的公理证明事物，它不知道如何处理指数。对于下面的引理，我们将用引理 `exp_add x y` 重写两次，这是一个证明 `exp(x+y) = exp(x) * exp(y)` 的证明。

```lean
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add (a + b) c]
  rw [exp_add a b]

```

还要注意在第二个 `rw` 之后，目标变成了 `exp a * exp b * exp c = exp a * exp b * exp c`，Lean立即声明证明完成。

如果我们不为引理提供参数，Lean 将重写第一个匹配的子表达式。在我们的例子中这足够好了。有时需要更多控制。

```lean
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add, exp_add]

```

让我们做一个练习，你还需要使用 `exp_sub x y : exp(x-y) = exp(x) / exp(y)` 和 `exp_zero : exp 0 = 1`。

回想一下 `a + b - c` 意味着 `(a + b) - c`。

你可以使用 `ring` 或者用 `mul_one x : x * 1 = x` 重写来简化右边的分母。

```lean
example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  sorry

```

## 从右到左的重写

由于等式是对称关系，我们也可以使用 `←` 将等式的右边替换为左边，如下例所示。

```lean
example (a b c d e : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h, h']

```

每当你在 Lean 文件中看到一个你的键盘上没有的符号，比如 ←，你可以将鼠标光标放在上面，从工具提示中学习如何输入它。对于 ←，你可以通过输入 "\l " 来输入它，即反斜杠-l-空格。

注意从右到左的重写故事完全是关于你想要*使用*的等式中的边，而不是关于你想要*证明*的内容中的边。前面例子中的 `rw [← h]` 用左边替换了右边，所以它在当前目标中寻找 `b + c` 并用 `a` 替换它。

```lean
example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  sorry

```

## 在局部假设中重写

我们也可以在局部上下文的假设中执行重写，例如使用
  `rw [exp_add x y] at h`
来在假设 `h` 中将 `exp(x + y)` 替换为 `exp(x) * exp(y)`。

`exact` 策略允许你给出一个明确的证明项来证明当前目标。

```lean
example (a b c d : ℝ) (h : c = d*a + b) (h' : b = d) : c = d*a + d := by
  rw [h'] at h
  -- 我们的假设 `h` 现在正好是我们需要证明的
  exact h

```

## 使用calc的计算布局

上面例子中写的内容与我们在纸上写的相去甚远。现在让我们看看如何获得更自然的布局（并且也回到使用 `ring` 而不是显式引理调用）。在下面每个 `:=` 后，目标是证明与前一行的等式（或第一行的左边）。仔细检查你是否理解这一点，方法是将光标放在每个 `by` 后并查看策略状态。

```lean
example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring

```

让我们做一些使用 `calc` 的练习。

```lean
example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by sorry
              _ = exp ((b + b) + (c + c))           := by sorry
              _ = exp (b + b) * exp (c + c)         := by sorry
              _ = (exp b * exp b) * (exp c * exp c) := by sorry
              _ = (exp b) ^ 2 * (exp c)^2           := by sorry

```

从实用的角度来看，编写这样的证明时，有时很方便：
* 通过点击Lean Infoview面板右上角的暂停图标按钮暂停VScode中的策略状态视图更新。
* 写出完整的计算，每行以":= ?_"结尾
* 通过点击播放图标按钮恢复策略状态更新并填入证明。

下划线应该放在 `calc` 下面第一行的左边。对齐等号和 `:=` 符号不是必需的，但看起来整洁。

```lean
example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by
  sorry

```

恭喜，这是你的第一个练习文件的结尾！你已经看到了输入 Lean 证明的样子，并学习了以下策略：
* `ring`
* `rw`
* `exact`
* `calc`
