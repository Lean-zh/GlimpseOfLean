```lean
import GlimpseOfLean.Library.Short

```

# Lean 快速入门

这个文件是 Glimpse of Lean 项目的简短版本。它适合那些想要花费两个小时来了解 Lean 的人。希望两个小时足够至少完成关于实数数列极限的首批练习。如果你进度较快或有更多时间，可以尝试完成所有这些练习。

当然，由于我们的目标是尽量减少需要解释的内容，同时仍然让人了解 Lean 是如何看待数学证明的，这里的证明并不总是最符合惯用法的。

每个用来推进证明的命令都被称为"策略"(tactic)。我们将学习其中的十几个。对于每个策略，我们会看到几个例子，然后你将有练习要做。每个练习的目标是将单词 `sorry` 替换为一系列策略，使 Lean 报告没有剩余目标，且过程中不报告任何错误。

## 计算

我们从使用实数的基本计算开始。我们可以进行微观管理游戏，调用加法的交换律和结合律等性质。但我们也可以要求 Lean 使用 `ring` 策略来处理任何仅使用这些性质的证明。通过"仅这些性质"，我们特别是指它不会使用任何特定于当前证明的假设。

单词 `ring` 指的是抽象数学定义，它封装了加法、减法和乘法的基本性质。这里不需要了解这个抽象代数的知识。

```lean
example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  ring

```

现在轮到你了：将单词 sorry 替换为相关的策略来完成练习。

```lean
example (a b : ℝ) : (a+b)*(a-b) = a^2 - b^2 := by
  -- sorry
  ring
  -- sorry

```

我们的下一个策略是 `congr` 策略（`congr` 代表"同余"）。它试图通过比较两边并在每次看到不匹配时创建新目标来证明等式。

```lean
example (a b : ℝ) (f : ℝ → ℝ) : f ((a+b)^2) = f (a^2 + 2*a*b + b^2) := by
  congr
  -- `congr` 识别出模式 `f _ = f _` 并创建了一个新目标
  -- 关于不匹配的部分，即提供给 `f` 的参数。
  ring

```

在下一个例子中试试。

```lean
example (a b : ℝ) (f : ℝ → ℝ) : f ((a+b)^2 - 2*a*b) = f (a^2 + b^2) := by
  -- sorry
  congr
  ring
  -- sorry

```

当存在多个不匹配时，`congr` 会创建多个目标。有时它会过于热情，匹配"太多"。例如，如果目标是 `f (a+b) = f (b+a)`，那么 `congr` 会识别出通用模式 `f (_ + _) = f (_ + _)` 并创建两个目标：`a = b` 和 `b = a`。这可以通过各种方式控制。最基本的方式对我们来说就足够了：我们可以通过在 `congr` 后放一个数字来限制函数应用层数。在示例中，应用的两个函数是 `f` 和加法，我们只想通过 `f` 的应用。

```lean
example (a b : ℝ) (f : ℝ → ℝ) : f (a + b) = f (b + a) := by
  congr 1 -- 尝试移除那个 1 或增加它来查看问题。
  ring

```

实际上 `congr` 不仅仅是找到不匹配，它还尝试使用假设来解决它们。在下一个例子中，`congr` 通过匹配创建目标 `a + b = c`，然后立即通过注意到并使用假设 `h` 来证明它。

```lean
example (a b c : ℝ) (h : a + b = c) (f : ℝ → ℝ) : f (a + b) = f c := by
  congr

```

策略 `ring` 和 `congr` 是我们用来计算的基本工具。但有时我们需要连接几个计算步骤。这是 `calc` 策略的工作。

在下面的例子中，仔细考虑在 `calc` 行后每个 `by` 后显示的策略状态是有帮助的。

```lean
example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by congr
    _ = b*a - a*b := by congr
    _ = 0         := by ring

```

注意每个 `_` 代表前一行的右边。因此我们实际上是在证明一系列等式，然后 `calc` 策略负责应用等式的传递性（或在证明不等式时应用等式和不等式）。这个序列中的每个证明都由 `:= by` 引入。

`calc` 的缩进规则有点微妙，特别是当 `calc` 后还有其他策略时。要小心始终对齐 `_`。对齐等号和 `:=` 符号看起来很好，但不是强制性的。

在更大的例子中，布置这些计算步骤并复制粘贴公共片段可能有点繁琐，但我们得到了 calc widget 的帮助，如视频中所示：

https://www.imo.universite-paris-saclay.fr/~patrick.massot/calc_widget.webm

如你在那里看到的，`calc?` 策略提议创建一行计算，然后将光标放在 `:= by` 后允许选择子项以在新的计算步骤中替换。

注意子项选择是使用 Shift-click 完成的。没有"点击并移动光标然后停止点击"。这与你编辑器或浏览器中的常规文本选择不同。

```lean
example (a b c : ℝ) (h : a = -b) (h' : b + c = 0) : b*(a - c) = 0 := by
  -- sorry
  calc
    b*(a - c) = b*(-b - c) := by congr
    _         = -b*(b + c) := by ring
    _         = -b*0       := by congr
    _         = 0          := by ring
  -- sorry

```

我们也可以使用 `gcongr`（代表"广义同余"）而不是 `congr` 来处理不等式。

```lean
example (a b : ℝ) (h : a ≤ 2*b) : a + b ≤ 3*b := by
  calc
    a + b ≤ 2*b + b := by gcongr
    _     = 3*b     := by ring

example (a b : ℝ) (h : b ≤ a) : a + b ≤ 2*a := by
  -- sorry
  calc
    a + b ≤ a + a := by gcongr
    _     = 2*a   := by ring
  -- sorry

```

你在计算中将使用的最后一个策略是简化器 `simp`。它会重复应用标记为可简化引理的多个引理。例如，下面的证明将 `x - x` 简化为 `0`，然后将 `|0|` 简化为 `0`。

```lean
example (x : ℝ) : |x - x| = 0 := by
  simp


```

## 全称量词和蕴含

现在让我们学习关于 `∀` 量词。

设 `P` 是类型 `X` 上的谓词。这意味着对于每个类型为 `X` 的数学对象 `x`，我们得到一个数学陈述 `P x`。

Lean 将 `∀ x, P x` 的证明 `h` 看作一个函数，将任何 `x : X` 发送到 `P x` 的证明 `h x`。这里已经演示了使用 `∀` 开头假设或引理的方法：我们可以简单地向它提供相关 `X` 的一个元素。

注意我们不需要在表达式 `∀ x, P x` 中拼写出 `X`，只要 `P` 的类型对 Lean 来说是清楚的，它就可以推断 `x` 的类型。

让我们定义一个谓词来玩 `∀`。在这个例子中我们有一个函数 `f : ℝ → ℝ`，`X = ℝ`（这里不用写 `f (x : ℝ)`，由于 `X` 的值能从 `f` 是 `ℝ` 到 `ℝ` 的函数这个事实推断出来）。

```lean
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

```

在上述定义中，注意在 `f x` 中没有括号。这是 Lean 表示函数应用的方式。在 `f (-x)` 中有括号是为了防止 Lean 看到 `f` 和 `x` 的减法（这没有意义）。还要小心 `f` 和 `(-x)` 之间的空格是强制的。

`apply` 策略可以用来特化全称量词的陈述。

```lean
example (f : ℝ → ℝ) (hf : even_fun f) : f (-3) = f 3 := by
  apply hf 3

```

幸运的是，Lean 足够智能，我们省略 `3` 也能通过。`apply` 策略会比较目标与假设并决定将其特化为 `x = 3`。

```lean
example (f : ℝ → ℝ) (hf : even_fun f) : f (-3) = f 3 := by
  apply hf

```

在下面的练习中，你可以选择是否要 Lean 的帮助还是自己做所有工作。

```lean
example (f : ℝ → ℝ) (hf : even_fun f) : f (-5) = f 5 := by
  -- sorry
  apply hf
  -- sorry

```

这是关于使用 `∀` 的。现在让我们看看如何证明 `∀`。

为了证明 `∀ x, P x`，我们使用 `intro x₀` 来固定一个任意的类型为 `X` 的对象，并称其为 `x₀`（`intro` 代表"引入"）。注意我们不必使用字母 `x₀`，任何名称都可以。

我们将证明实数余弦函数是偶函数。在引入一些 `x₀` 后，简化器策略可以完成证明。记得仔细检查每行开头的目标。

```lean
open Real in -- 这一行声明我们指的是实数 cos，而不是复数的。
example : even_fun cos := by
  intro x₀
  simp

```

为了得到稍微更有趣的例子，我们将同时使用和证明一些全称量词的陈述。

在下一个证明中，我们也借机介绍了 `unfold` 策略，它只是展开定义。这里这纯粹是出于教学目的，Lean 不需要这些 `unfold` 调用。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- 我们关于 f 是偶函数的假设意味着 ∀ x, f (-x) = f x
  -- unfold even_fun at * -- 对所有位置的展开定义
  unfold even_fun at hf -- 注意 `hf` 在这一行后如何变化
  -- 对 g 也是如此
  unfold even_fun at hg
  -- 我们需要证明 ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- 设 x₀ 为任意实数
  intro x₀
  -- 让我们计算
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g (-x₀)     := by congr 1; apply hf
  -- 将光标放在前一行中 `;` 和 `apply` 之间以查看中间目标
    _             = f x₀ + g x₀        := by congr 1; apply hg
    _             = (f + g) x₀         := by simp


```

像 `congr` 和 `ring` 这样的策略不会展开出现在目标中的定义。这就是为什么第一个行是必要的，尽管它只是展开加法定义。然而，最后一行不是必要的，因为它只是证明按定义为真的东西，并且没有被任何其他策略跟随。

还注意 `congr` 可以生成多个目标，所以我们不必调用它两次。

因此我们可以将上述证明压缩为：

```lean
example (f g : ℝ → ℝ)  (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  intro x₀
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g x₀        := by congr 1; apply hf; apply hg

```

如果你宁愿展开证明，可以使用 `specialize` 策略在使用它之前特化全称量词的假设。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- 设 x₀ 为任意实数
  intro x₀
  specialize hf x₀ -- hf 现在只与 x₀ 相关
  specialize hg x₀ -- hg 现在只与 x₀ 相关
  -- 让我们计算
  -- （注意 `congr` 现在如何找到假设来完成这些步骤）
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g (-x₀)     := by congr
    _             = f x₀ + g x₀        := by congr
    _             = (f + g) x₀         := by simp

```

现在让我们练习。如果你需要学习如何输入 unicode 符号，可以将鼠标光标放在符号上方并等待一秒钟。回想一下，你可以通过给 `congr` 一个数字（如 `congr 1`）来设置深度限制。

还注意，如果你想节省一些输入，你可以称你的任意实数为 `x` 而不是 `x₀`。我们称其为 `x₀` 只是为了强调它不需要与陈述中的符号相同。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  -- sorry
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x))   := by simp
    _            = g (f x)      := by congr 1; apply hf
  -- sorry

```

现在让我们将全称量词与蕴含结合起来。

在下一个定义中，注意 `∀ x₁, ∀ x₂, ...` 如何缩写为 `∀ x₁ x₂, ...`。

```lean
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

```

注意 Lean 如何使用单箭头 `→` 来表示蕴含。这与 `f : ℝ → ℝ` 中的箭头相同。实际上 Lean 将蕴含 `P → Q` 的证明看作从 `P` 的证明到 `Q` 的证明的函数。

因此假设 `hf : non_decreasing f` 是一个函数，它以两个数字和它们之间的不等式为输入，并输出它们在 `f` 下的像之间的不等式。

```lean
example (f : ℝ → ℝ) (hf : non_decreasing f) (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂) : f x₁ ≤ f x₂ := by
  apply hf x₁ x₂ hx

```

我们可以要求 Lean 为我们做更多工作，如下例所示：

```lean
example (f : ℝ → ℝ) (hf : non_decreasing f) (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂) : f x₁ ≤ f x₂ := by
  apply hf -- Lean 比较目标与假设 `hf`。它识别出 `hf`
           -- 需要特化为给定的数字 `x₁` 和 `x₂`，以得到
           -- 蕴含 `x₁ ≤ x₂ → f x₁ ≤ f x₂`，然后要求前提 `x₁ ≤ x₂` 的证明
  apply hx -- 我们的假设 hx 就是这样一个证明

```

注意策略 `apply` 不意味着任何模糊的东西，如"以某种方式使用那个表达式"。它要求一个输入，该输入要么是完整的证明如第一个例子，要么是涉及全称量词和蕴含在某个陈述前面的证明，该陈述可以特化为当前目标（如前一个例子）。

在这个非常简单的例子中，我们没有获得太多。现在比较下面相同陈述的两个证明。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ hx -- 注意 `intro` 如何也引入假设 `h : x₁ ≤ x₂`
  apply hg (f x₁) (f x₂) (hf x₁ x₂ hx)

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ hx
  apply hg
  apply hf
  apply hx

```

花一些时间理解在第二个证明中，Lean 如何为我们省去了寻找相关数字对的麻烦，也很好地将证明切成片段。你可以在下面的变体中选择你的方式。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by
  -- sorry
  intro x₁ x₂ hx
  apply hg (f x₁) (f x₂) (hf x₁ x₂ hx)
  -- sorry

```

在这个阶段，你应该感觉到这样的证明实际上不需要任何思考。实际上 Lean 可以轻松地在一个策略中处理完整的证明（但我们这里不需要这个）。

我们也可以使用 `specialize` 策略在使用假设之前向其提供参数，正如我们在偶函数例子中看到的那样。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g + f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  specialize hg x₁ x₂ h
  calc
    (g + f) x₁ = g x₁ + f x₁ := by simp
    _          ≤ g x₂ + f x₂ := by gcongr
    _          = (g + f) x₂  := by simp


```

# 寻找引理

Lean 的数学库包含许多有用的事实，记住所有引理的名字是不可行的。我们已经看到了简化器策略 `simp`，它应用许多引理而不使用它们的名称。

使用 `simp` 来证明以下内容。注意 `X : Set ℝ` 意味着 `X` 是一个只包含实数的集合。

```lean
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  -- sorry
  simp
  apply hx
  -- sorry

```

`apply?` 策略将从库中找到引理并告诉你它们的名称。它在目标显示下方创建一个建议。你可以点击这个建议来编辑你的代码。使用 `apply?` 找到每个具有紧支撑的连续函数都有全局最小值的引理。

```lean
example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by
  -- sorry
  -- 使用 `apply?` 找到：
  exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f
  -- sorry

```

## 存在量词

为了证明 `∃ x, P x`，我们用 `use x₀` 给出一些有效的 `x₀`，然后证明 `P x₀`。这个 `x₀` 可以是来自局部上下文的对象或更复杂的表达式。在下面的例子中，要在 `use` 后检查的性质按定义为真，所以证明结束了。

```lean
example : ∃ n : ℕ, 8 = 2*n := by
  use 4

```

为了使用 `h : ∃ x, P x`，我们使用 `rcases` 策略来固定一个有效的 `x₀`。

同样 `h` 可以直接来自局部上下文或可以是一个更复杂的表达式。

例子将在 `ℤ` 中使用整除（注意 `∣` 符号不是 ASCII 而是 unicode 符号）。在单词 `with` 后出现的尖括号也是 unicode 符号。如果你的键盘没有配置为直接输入这些符号，你可以将鼠标光标放在符号上方并等待一秒钟来查看如何在这个编辑器中输入它们。


```lean
example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  rcases h₁ with ⟨k, hk⟩ -- 我们固定一些 `k` 使得 `b = a * k`
  rcases h₂ with ⟨l, hl⟩ -- 我们固定一些 `l` 使得 `c = b * l`
  -- 由于 `a ∣ c` 意味着 `∃ k, c = a*k`，我们需要 `use` 策略。
  use k*l
  calc
    c = b*l     := by congr
    _ = (a*k)*l := by congr
    _ = a*(k*l) := by ring

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c := by
  -- sorry
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨l, hl⟩
  use k+l
  calc
    b + c = a*k + a*l     := by congr
    _     = a*(k + l)     := by ring
  -- sorry

```

## 合取

我们现在解释如何处理另一个逻辑概念：合取。

给定两个陈述 `P` 和 `Q`，合取 `P ∧ Q` 是 `P` 和 `Q` 都为真的陈述（`∧` 有时被称为"逻辑与"）。

为了证明 `P ∧ Q`，我们使用 `constructor` 策略，它将目标分割为证明 `P` 然后证明 `Q`。

为了使用 `P ∧ Q` 的证明 `h`，我们使用 `h.1` 来得到 `P` 的证明和 `h.2` 来得到 `Q` 的证明。我们也可以使用 `rcases h with ⟨hP, hQ⟩` 来得到 `hP : P` 和 `hQ : Q`。

让我们在一个非常基本的逻辑证明中看到两者的作用：让我们从 `P ∧ Q` 推导出 `Q ∧ P`。

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  apply h.2
  apply h.1

```

## 极限

我们学习了足够的策略来操作涉及两种量词的定义：实数序列的极限。


- 我们称序列 `u` 收敛到极限 `l`，如果以下成立。

```lean
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

```

让我们看一个使用我们上面看到的许多策略的例子：如果 `u` 是值为 `l` 的常数，那么 `u` 趋于 `l`。

记住 `apply?` 可以找到你不想记住名称的引理，比如说正数蕴含非负数的引理。

```lean
example (h : ∀ n, u n = l) : seq_limit u l := by
  intro ε ε_pos
  use 0
  intro n hn
  calc |u n - l| = |l - l| := by congr; apply h
    _            = 0       := by simp
    _            ≤ ε       := by apply? -- exact le_of_lt ε_pos

```

在处理绝对值时，我们将使用引理：

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

在处理 max 时，我们将使用

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

我们使用这些引理的方式是用重写命令 `rw`。让我们看一个例子。在上边的例子中，我们保留了 `apply?` 而不是接受其建议，以便强调不需要记住这些引理名称。还注意我们如何可以在任何地方使用 `by` 开始使用策略证明某些东西。在下面的例子中，我们使用它来从我们的假设 `ε > 0` 证明 `ε/2 > 0`。

```lean
-- 如果 `u` 趋于 `l` 和 `v` 趋于 `l'`，那么 `u+v` 趋于 `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intro ε ε_pos
  rcases hu (ε/2) (by apply?) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by apply?) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rw [ge_max_iff] at hn -- 注意 hn 如何从 `n ≥ max N₁ N₂` 变为 `n ≥ N₁ ∧ n ≥ N₂`
  specialize hN₁ n hn.1
  specialize hN₂ n hn.2
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := by simp
    _ = |(u n - l) + (v n - l')|                      := by congr; ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply?
    _ ≤ ε/2 + ε/2                                     := by gcongr
    _ = ε                                             := by simp


```

让我们做类似的事情：使用 `ge_max_iff` 和 `abs_le` 的夹逼定理。你可能想要在几个假设以及目标中使用 `abs_le` 重写。你可以为此使用 `rw [abs_le] at *`。

```lean
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
  -- sorry
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  rcases hw ε ε_pos with ⟨N', hN'⟩
  use max N N'
  intro n hn
  rw [ge_max_iff] at hn
  specialize hN n hn.1
  specialize hN' n hn.2
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor
  calc
    -ε ≤ u n - l := by apply hN.1
    _ ≤ v n - l  := by gcongr
  calc
    v n - l ≤ w n - l := by gcongr
          _ ≤ ε := by apply hN'.2
  -- sorry


```

在下一个练习中，我们将使用

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

作为第一步。

```lean
-- 序列最多有一个极限。你将能够在以下练习中使用那个引理
-- 练习。
lemma uniq_limit (hl : seq_limit u l) (hl' : seq_limit u l') : l = l' := by
  apply eq_of_abs_sub_le_all
  -- sorry
  intro ε ε_pos
  rcases hl (ε/2) (by apply?) with ⟨N, hN⟩
  rcases hl' (ε/2) (by apply?) with ⟨N', hN'⟩
  calc
    |l - l'| ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply?
           _ = |u (max N N') - l| + |u (max N N') - l'| := by congr 1; apply?
           _ ≤ ε/2 + ε/2 := by gcongr; apply hN; apply?; apply hN'; apply?
           _ = ε := by simp
  -- sorry

```


## 子序列

我们现在将玩子序列。

我们称 `φ : ℕ → ℕ` 是一个提取，若它是（严格）递增的。

```lean
def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

```

在以下内容中，`φ` 总是表示从 `ℕ` 到 `ℕ` 的函数。

下一个引理通过简单的归纳证明，但我们在本教程中没有看到归纳。如果你做过自然数游戏，那么你可以删除下面的证明并尝试重构它。否则你可以简单地快速查看归纳证明的样子（但我们这里不需要任何其他的）。

- 提取大于恒等函数

```lean
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by
  intro hyp n
  induction n with
  | zero =>  apply?
  | succ n ih => exact Nat.succ_le_of_lt (by
      calc n ≤ φ n := ih
        _    < φ (n + 1) := by apply hyp; apply?)

```

在练习中，我们使用 `∃ n ≥ N, ...`，这是 `∃ n, n ≥ N ∧ ...` 的缩写。

不要忘记移动光标查看每个 `apply?` 在证明什么。

- 提取对任意大的输入取任意大的值。

```lean
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  -- sorry
  intro h N N'
  use max N N'
  constructor
  apply?
  calc
    N ≤ max N N' := by apply?
    _ ≤ φ (max N N') := by apply?
  -- sorry

```

- 我们称实数 `a` 是序列 `u` 的聚点，若 `u` 有一个收敛到 `a` 的子序列。

```lean
def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

```

- 如果 `a` 是 `u` 的聚点，那么对任意大的输入，`u` 的值任意接近 `a`。

```lean
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  -- sorry
  intro hyp ε ε_pos N
  rcases hyp with ⟨φ, φ_extr, hφ⟩
  rcases hφ ε ε_pos with ⟨N', hN'⟩
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩
  use φ q
  constructor
  apply hq'
  apply hN' _ hq
  -- sorry


```

- 如果 `u` 趋于 `l`，那么它的子序列趋于 `l`。

```lean
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
  seq_limit (u ∘ φ) l := by
  -- sorry
  intro ε ε_pos
  rcases h ε ε_pos with ⟨N, hN⟩
  use N
  intro n hn
  apply hN
  calc
    N ≤ n := by apply?
    _ ≤ φ n := id_le_extraction' hφ n
  -- sorry

```

- 如果 `u` 趋于 `l`，那么它的所有聚点都等于 `l`。

```lean
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by
  -- sorry
  rcases ha with ⟨φ, φ_extr, lim_u_φ⟩
  apply uniq_limit
  apply lim_u_φ
  apply?
  -- sorry

```

- `u` 是柯西序列，如果对足够大的输入，它的值变得任意接近。

```lean
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by
  -- sorry
  intro hyp
  rcases hyp with ⟨l, hl⟩
  intro ε ε_pos
  rcases hl (ε / 2) (by apply?) with ⟨N, hN⟩
  use N
  intro p q hp hq
  calc
    |u p - u q| = |u p - l + (l - u q)| := by congr; ring
    _ ≤ |u p - l| + |l - u q| := by apply?
    _ = |u p - l| + |u q - l| := by congr 1; apply?
    _ ≤ ε/2 + ε/2 := by gcongr; apply?; apply?
    _ = ε := by simp
  -- sorry

```