```lean
import GlimpseOfLean.Library.Basic

namespace Introduction

```

# 本教程的介绍

如果你的屏幕较小且正在 VSCode 中阅读此文件，你可以按下 `alt-Z`（或 `option-Z`）来启用自动换行。

欢迎来到这个设计用于让你在几小时内一窥 Lean 的教程。

首先让我们看看 Lean 证明长什么样子，暂时不用理解任何语法细节。你不需要在这个文件中输入任何内容。

如果一切正常，你现在应该在文本右边看到一个面板，显示类似"No info found."的消息。这个面板将在证明内部开始显示有趣的内容。

请注意，任何在 `/-` 和 `

```lean
` 之间或在 `--` 之后的文本都是注释是为你准备的，Lean 会忽略这些内容。

首先让我们回顾两个微积分定义。
-/

```

- 如果对于任意 ε > 0，存在 N，使得对所有 n ≥ N，有 |u_n - l| ≤ ε，则实数序列 `u` 收敛到 `l`。这个条件将写作 `seq_limit u l`。

```lean
def seq_limit (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

```

在上面的定义中，注意序列 `u` 的第 `n` 项简单地记作 `u n`。

类似地，在下一个定义中，`f x` 就是我们在纸上写的 `f(x)`。另请注意，蕴含用单箭头表示（我们稍后会解释原因）。

更加微妙的是，我们写 `l : ℝ` 来表示 `l` 是一个实数，而你在纸上可能会写 `l ∈ ℝ`。

- 我们称函数 `f : ℝ → ℝ` 在 `x₀` 处连续，若 `∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`。
这个条件将写作 `continuous_at f x₀`。

```lean
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

```

- 现在我们声明，如果 `f` 在 `x₀` 处连续，那么它在 `x₀` 处序列连续：对于任何收敛到 `x₀` 的序列 `u`，序列 `f ∘ u` 收敛到 `f x₀`。
下一行的所有内容都描述了对象和假设，每个都有其名称。
接下来的行是我们需要证明的断言。

```lean
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
  seq_limit (f ∘ u) (f x₀) := by -- 这个 `by` 关键字标志着证明的开始
  -- 将你的文本光标放在这里并观察右侧的面板。
  -- 蓝色 `⊢` 符号右边是我们试图证明的内容。在此之上
  -- 是我们的变量和假设列表。当你阅读证明时，将光标从一行移动到另一行
  -- （例如使用下箭头键）并观察面板的变化。

  -- 我们的目标是证明，对于任何正数 `ε`，存在一个自然数
  -- `N`，使得对于任何至少为 `N` 的自然数 `n`，
  -- `|f(u_n) - f(x₀)|` 至多为 `ε`。
  unfold seq_limit
  -- 固定一个正数 `ε`。
  intros ε hε
  -- 根据关于 `f` 应用于这个正数 `ε` 的假设，我们得到一个正数 `δ`
  -- `Hf`: 使得对于所有实数 `x`，如果 `|x - x₀| ≤ δ`，那么 `|f(x) - f(x₀)| ≤ ε` (1)。
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- 关于 `u` 应用于这个 `δ` 的假设给出一个自然数 `N`，使得
  -- `Hu`: 对于每个自然数 `n`，如果 `n ≥ N`，那么 `|u_n - x₀| ≤ δ`   (2)。
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- 让我们证明 `N` 即为所求。
  use N
  -- 对于任意 `n`，满足 `n ≥ N`，我们证明 `|f(u_n) - f(x₀)| ≤ ε`。
  intros n hn
  -- 将 (1) 应用于 `u_n`，我们只需要证明 `|u_n - x₀| ≤ δ`。
  apply Hf
  -- 由性质 (2) 和我们关于 `n` 的假设立得。
  apply Hu n hn
  -- 证明完成！


```

现在这个证明结束了，你可以选择短版路径或长版路径。如果你想在 lean4web 服务器上做短版路径，你应该访问
https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FShorter.lean。

如果你使用本地安装或 GitPod 或 Codespaces 跟随长版路径，你应该使用此面板左侧的文件浏览器打开文件 `Exercises > 01Rewriting.lean`。
