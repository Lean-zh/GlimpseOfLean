

import GlimpseOfLean.Library.Basic
import Mathlib.Data.Complex.Exponential
open Real

/- # 计算

## ring 策略

在学习数学的过程中，我们最早接触的证明类型之一就是通过计算来证明。尽管这听起来不像是一种证明，但其实我们是在使用表达数字运算性质的引理。当然，我们通常不想显式地调用这些引理，因此 mathlib 有一个名为 `ring` 的策略，用来处理通过应用所有交换环的性质所得出的等式证明。
-/

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
}

/- 现在轮到你了，把下面的 sorry 替换成一段证明。在这里，证明只是 `ring`。
在你完成证明后，你会看到一个小巧的 "无目标" 消息，这表示你的证明已经完成。
-/

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by {
  -- sorry
  ring
  -- sorry
}

/- 在上述的第一个例子中，仔细观察 Lean 在何处展示圆括号。  
`ring` 策略肯定知道乘法的结合性，但有时了解二元运算真的是二元的，像 `a*b*c` 这样的表达式被 Lean 解读为 `(a*b)*c` ，这样的事实才是等于 `a*(b*c)` 的引理
是在需要时由 `ring` 策略使用的。
-/

/- ## 重写策略

现在让我们看看如何使用涉及的数字的假设进行计算。这使用了等式的基本属性：如果两个数学对象 A 和 B 是相等的，那么在任何涉及 A 的声明中，我们都可以用 B 替换 A。这个操作被称为重写，而在 Lean 中，这个策略的命令是 `rw`。请仔细研究下面的证明，并尝试理解里面发生了什么。

-/

example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h]
  rw [h']
  ring
}

/- 注意 `rw` 策略会改变当前的目标。在上述证明的第一行之后，新的目标是 `b + c + e = d + c`。所以你可以将这个第一步证明读作："我想要证明， `a + e = d + c`，但是，由于假设 `h` 告诉我 `a = b + c`，所以只需要证明 `b + c + e = d + c` 就可以了。"

实际上，一个命令可以做多个重写。
-/

example (a b c d : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h, h']
  ring
}

/- 请注意，将光标放在`h`和`h'`之间可以展示你的中间证明状态。

也要注意策略状态中微妙的背景颜色变化，绿色显示新增加的内容，红色显示即将改变的内容。

现在你自己试试。请注意，尽管 ring 仍然可以做计算，但是它并不使用假设`h`和`h'`。
-/

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by {
  -- sorry
  rw [h', h]
  ring
  -- sorry
}

/- ## 使用引理重写

在前面的例子中，我们利用了局部假设来重写目标。但我们也可以使用引理。例如，让我们证明一个关于指数运算的引理。
由于 `ring` 只知道如何从环的公理证明事情，它不知道如何处理指数运算。
对于以下的引理，我们将使用引理 `exp_add x y` 进行两次重写，该引理是 `exp(x+y) = exp(x) * exp(y)` 的证据。
-/

example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add (a + b) c]
  rw [exp_add a b]
}

/- 请注意，在第二次执行 `rw` 之后，目标变成了
`exp a * exp b * exp c = exp a * exp b * exp c` ，然后 Lean 立即声明证明已完成。

如果我们不向引理提供参数，Lean 将重写第一个匹配
子表达式。在我们的例子中这已经足够了。有时候需要更多的控制。
-/

example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add, exp_add]
}

/- 我们来做一个练习，你也需要使用
`exp_sub x y : exp(x-y) = exp(x) / exp(y)` 和 `exp_zero : exp 0 = 1`。

请记住，`a + b - c` 表示 `(a + b) - c`。

你可以使用 `ring` 或者通过 `mul_one x : x * 1 = x` 简化右侧的分母。
-/

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by {
  -- sorry
  rw [exp_sub, exp_add, exp_zero, mul_one]
  -- sorry
}

/- ## 从右到左重写

由于相等关系是一种对称关系，我们也可以使用 `←` 将等式的右侧替换为左侧，如下例所示。
-/

example (a b c : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by {
  rw [← h, h']
}

/- 无论何时，当你在 Lean 文件中看到一些你键盘上没有的符号，例如←，
你都可以将鼠标光标放在上面，然后从工具提示中学习如何输入它。
对于←，你可以通过输入 "\l " 来输入，也就是反斜杠-l-空格。

请注意，这种从右到左的重新书写的故事都是关于你想要
*使用*的等式的哪一边，而不是你想要*证明*的等式的哪一边。`rw [← h]` 将会将右手边替换为左手边，所以它将在当前的目标中寻找 `b + c` 并以 `a` 替换它。
-/

example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by {
  -- sorry
  rw [← h', ← h, ← h'']
  -- sorry
}

/- ## 在局部假设中重写

我们也可以在局部上下文的假设中进行重写，例如使用
  `rw [exp_add x y] at h`
来在假设 `h` 中将 `exp(x + y)` 替换为 `exp(x) * exp(y)`。

`exact` 策略允许你给出一个明确的证明项来证明当前的目标。
-/

example (a b c d : ℝ) (h : c = d*a - b) (h' : b = a*d) : c = 0 := by {
  rw [h'] at h
  ring at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h
}

/- ## 使用 calc 布局计算

上述示例中的内容与我们在纸上写的内容相差甚远。现在让我们看看如何得到更自然的布局（并且还要回到使用 `ring` 而不是显式引述引理）。在下面的每个 `:=` 后面，目标是证明等式与前一行（或第一行的左手边）相等。仔细检查你是否理解了这一点，方法是将你的光标放在每个 `by` 后面，然后查看策略状态。
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by {
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring
}

/- 我们来使用 `calc` 做一些练习。
-/

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by {
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by rw [h]
              _ = exp ((b + b) + (c + c))           := by ring
              _ = exp (b + b) * exp (c + c)         := by rw [exp_add]
              _ = (exp b * exp b) * (exp c * exp c) := by rw [exp_add, exp_add]
              _ = (exp b) ^ 2 * (exp c)^2           := by ring
}

/- 从实用的角度来看，编写这样的证明时，有时候可以：
* 通过点击 Lean Infoview 面板右上角的暂停图标按钮，暂停 VScode 中的 tactic 状态视图更新。
* 编写完整的计算，每行都以 ":= ?_" 结束
* 点击播放图标按钮，恢复 tactic 状态更新，然后填入证明内容。

下划线应放在 `calc` 下第一行的左手边。
等号和 `:=` 对齐并不是必需的，但看起来更整齐。
-/

example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by {
  -- sorry
  calc
    c = d*a + b   := by rw [h]
    _ = d*a + a*d := by rw [h']
    _ = 2*a*d     := by ring
  -- sorry
}

/- 恭喜你，这是你首个练习文件的结束！你已经看到了 Lean 证明的书写方式，并已经了解了以下策略：
* `ring`
* `rw`
* `exact`
* `calc`
-/

/- 
-/