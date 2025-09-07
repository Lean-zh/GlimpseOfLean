```lean
import GlimpseOfLean.Library.Basic

```

# 蕴含关系

## 使用蕴含关系

Lean 使用符号 `→` 而不是 `⇒` 来表示蕴含关系，因为它将 `P → Q` 的证明视为一个函数，将 `P` 的任何证明发送到 `Q` 的证明（如果看不清 → 和 ⇒ 的区别，请增大字体大小）。

例如，给定一个实数 `a`，引理 `sq_pos_of_pos` 声明 `0 < a → 0 < a^2` 所以下面的证明将"函数" `sq_pos_of_pos` 应用到假设 `ha` 上。

请记住，当你在 Lean 文件中看到键盘上没有的符号时，比如 →，你可以将鼠标光标放在它上面，从工具提示中了解如何输入它。对于 →，你可以通过输入 "\to " 来输入它，即反斜杠-t-o-空格。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by
  exact sq_pos_of_pos ha

```

上面的证明是直接证明：我们已经知道 `0 < a`，并将这个事实输入到蕴含关系中。我们也可以使用 `apply` 策略进行反向推理。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  apply sq_pos_of_pos -- 通过 `sq_pos_of_pos`，只需证明 `0 < a^2`
  apply sq_pos_of_pos -- 通过 `sq_pos_of_pos`，只需证明 `0 < a`
  exact ha -- 这正好是我们的假设 `ha`。

```

尝试使用引理 `add_pos : 0 < x → 0 < y → 0 < x + y` 来完成下一个练习。注意，在你 `apply add_pos` 之后你将有两个目标，需要一个一个地证明。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  sorry

```

你也可以使用 `have` 策略进行前向推理来给出证明。为了宣布一个中间陈述，我们使用：

  `have my_name : my_statement := by`

然后增加缩进级别。这会触发一个新目标的出现：证明这个陈述。证明完成后，该陈述将在名称 `my_name` 下可用。如果证明是单个 `exact` 策略，那么你可以去掉 `by` 和 `exact`，直接将 `exact` 的参数放在 `:=` 之后。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  have h2 : 0 < a^2 := by     -- 我们声明 `0 < a^2` 作为一个子目标
    apply sq_pos_of_pos  -- 我们开始证明子目标
    exact ha             -- 这行是缩进的，所以是子目标证明的一部分
  exact sq_pos_of_pos h2 -- 我们完成了子目标，现在使用它来证明主目标。

```

现在使用前向推理证明与之前相同的引理。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  sorry


```

## 证明蕴含关系

为了证明一个蕴含关系，我们需要假设前提并证明结论。这通过使用 `intro` 策略来完成。实际上上面的练习是在证明蕴含关系 `a > 0 → (a^2)^2 > 0`，但前提已经为我们引入了。

```lean
example (a b : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb -- 你可以在这里选择任意名称
  exact add_pos ha hb

```

现在证明命题逻辑中的以下简单陈述。注意 `p → q → r` 意味着 `p → (q → r)`。

```lean
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by
  sorry

```

注意，当使用 `intro` 时，你需要为假设给一个名称。Lean 允许你使用已经使用过的名称。在这种情况下，新的假设会隐藏现有的那个，使其变得不可访问。所以默认情况下安全的做法是使用新名称。

# 等价关系

## 使用等价关系重写陈述

在上一个文件中，我们看到了如何使用等式进行重写。对于数学陈述的类比操作是使用等价关系进行重写。这也是通过 `rw` 策略完成的。Lean 使用 `↔` 来表示等价关系，而不是 `⇔`（如果看不清区别，请增大字体大小）。

在以下练习中，我们将使用引理：

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`

```lean
example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [← sub_nonneg] -- 这个 `rw` 使用了一个等价关系
  have key : (c + b) - (c + a) = b - a := by
    ring
  rw [key] -- 这个 `rw` 使用了一个等式结果，不是等价关系
  rw [sub_nonneg] -- 然后我们切换回去以达到重言式 a ≤ b ↔ a ≤ b

```

让我们证明一个变化

```lean
example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by
  sorry

```

上面的引理已经在数学库中，名称为 `add_le_add_iff_right`：

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

这可以理解为："`add_le_add_iff_right` 是一个函数，它将一个实数 `c` 作为输入并输出 `a + c ≤ b + c ↔ a ≤ b` 的证明"。以下是使用此引理的示例。

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by rw [add_le_add_iff_right b] ; exact ha

```

## 将等价关系用作蕴含关系对

上面证明中的第二行有点愚蠢：我们使用陈述重写将目标简化为我们的假设 `ha`，但更自然的做法是将等价关系视为双向蕴含关系。我们可以通过 `h.1 : P → Q` 和 `h.2 : Q → P` 访问等价关系 `h : P ↔ Q` 的两个蕴含关系。这允许我们将上面的证明重写为：

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha


```

让我们使用 `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` 来做一个变化。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  sorry

```

重要提示：在前面的练习中，我们使用了像 `add_le_add_iff_left` 这样的引理作为操作等价关系的基本示例。但是在研究有趣的数学时手动调用这些引理会非常繁琐。有一些策略的工作就是自动完成这些事情，但这不是本文件的主题。


## 证明等价关系

为了证明一个等价关系，可以使用 `rw` 直到目标是重言式 `P ↔ P`，就像对等式所做的那样。

也可以使用 `constructor` 策略分别证明两个蕴含关系。下面是一个示例。如果你将光标放在 `constructor` 之后，你将看到两个目标，每个方向一个。Lean 会为你跟踪目标，确保你解决所有这些目标。"聚焦点" `·` 保持每个目标的证明分离。

```lean
example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by
  constructor
  · intro h
    calc
      a ^ 2 = b^2 + (a - b) * (a + b)  := by ring
          _ = b^2 + 0                  := by rw [h]
          _ = b^2                      := by ring
  · intro h
    calc
      (a-b)*(a+b) = a^2 - b^2  := by ring
                _ = b^2 - b^2  := by rw [h]
                _ = 0          := by ring


```

你可以在这个练习中自己尝试。

```lean
example (a b : ℝ) : a = b ↔ b - a = 0 := by
  sorry

```

这是本文件的结尾，在这里你学会了如何处理蕴含关系和等价关系。你学到了以下策略：
* `intro`
* `apply`
* `have`
* `constructor`
