```lean
import GlimpseOfLean.Library.Basic
```

# 含义

## 使用含义

Lean通过符号 `→` 表示含义，而非 `⇒` ，因为它将 `P → Q` 的证明视为一个函数，它可以将任何 `P` 的证明发送给 `Q` 的证明（如果你看不清→和⇒的区别，请增大字体大小）。

例如，给定一个实数 `a` ，引理 `sq_pos_of_pos` 声称 `0 < a → 0 < a^2`
所以下面的证明应用了 "函数" `sq_pos_of_pos` 到假设 `ha`。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by {
  exact sq_pos_of_pos ha
}
```

上述证明是一个直接证明：我们已知 `0 < a` 并将这个事实用于推理。
我们也可以使用 `apply` 策略进行反向推理。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a^2`
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a`
  exact ha -- this is exactly our assumption `ha`.
}
```

尝试使用引理 `add_pos : 0 < x → 0 < y → 0 < x + y` 来完成下一个练习。
注意，在你 `apply add_pos` 之后，你将会产生两个目标，你需要一个个去证明。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by {
  sorry
}
```

你也可以使用向前推理的方式，使用 `have` 策略来进行证明。
为了声明一个中间语句，我们使用：

  `have my_name : my_statement`

此操作会引发一个新目标的出现：证明该语句。证明需要以一个中心点 `·`（使用 `\.`输入）开始，且应对其进行缩进。
在证明完成后，该语句将以 `my_name` 的名字变得可用。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  have h2 : 0 < a^2      -- we declare `0 < a^2` as a subgoal
  · apply sq_pos_of_pos  -- we start proving the subgoal
    exact ha             -- this line is indented, so part of the proof of the subgoal
  exact sq_pos_of_pos h2 -- we finished the subgoal, and now we prove the main goal using it.
}
```

现在使用前向推理证明之前的引理。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by {
  sorry
}
```

## 证明推论

为了证明一个推论，我们需要假设前提并证明结论。
这是使用 `intro` 策略完成的。秘密地，上述练习是证明推论 `a > 0 → (a^2)^2 > 0` ，但是前提已经为我们介绍了。

```lean
example (a : ℝ) : a > 0 → b > 0 → a + b > 0 := by {
  intro ha hb -- You can choose any names here
  exact add_pos ha hb
}
```

现在，我们证明以下的命题逻辑简单陈述。
请注意，`p → q → r` 意味着 `p → (q → r)`。

```lean
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by {
  sorry
}
```

# 等价

## 使用等价关系重写陈述

在上一个文件中，我们看到了如何使用等式进行重写。 
用数学语句进行的类似操作是使用等价关系进行重写。 这也是使用 `rw` 策略完成的。
Lean 使用 `↔` 代替 `⇔` 来表示等价（如果看不清区别，请增大字体大小）。

在以下练习中，我们将使用以下引理：

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`

```lean
example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by {
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a -- Here we introduce an intermediate statement named key
  · ring   -- and prove it after a `·`
  rw [key] -- we can now use `key`. This `rw` uses an equality result, not an equivalence
  rw [sub_nonneg] -- and switch back to reach the tautology a ≤ b ↔ a ≤ b
}
```

我们来证明一个变种

```lean
example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by {
  sorry
}
```

上述引理已经存在于数学库中，名为 `add_le_add_iff_right` ：

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

这可以理解为：“ `add_le_add_iff_right` 是一个函数，它以一个实数 `c` 作为输入，并将输出 `a + c ≤ b + c ↔ a ≤ b` 的证明”。这里有一个使用这个引理的例子。

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by { rw [add_le_add_iff_right b] ; exact ha  }
}
```

## 将等价关系作为一对蕴含关系使用

在以上证明的第二行里，我们有点傻：我们使用命题重写来将目标简化为我们的假设 `ha`，但更自然的做法是将等价关系看作双向蕴含关系。我们可以访问等价关系 `h : P ↔ Q` 的两个蕴含 `h.1 : P → Q` 和 `h.2 : Q → P`。这允许我们将上述证明重写为：

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha
}
```

让我们用 `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` 进行一种变体。

Let's try it.

# proof
```lean
import data.int.basic

theorem add_left_cancel {a b c : ℕ} :
  a + b = a + c ↔ b = c :=
begin
  rw nat.add_comm a b,
  rw nat.add_comm a c,
  apply add_right_cancel,
end
```
...
And the result:
```
Lean check passed!
```

然后试试看。

# 证明
```lean
import data.int.basic

theorem add_left_cancel {a b c : ℕ} :
  a + b = a + c ↔ b = c :=
begin
  rw nat.add_comm a b,
  rw nat.add_comm a c,
  apply add_right_cancel,
end
```
...
结果如下：
```
Lean check 通过！
```

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by {
  sorry
}
```

## 证明等价

为了证明一个等价，你可以像处理等式一样，使用 `rw` 直到目标变成恒等式 `P ↔ P`。

你也可以分别证明这两个含义，使用 `constructor` 策略。

以下是一个例子。

```lean
example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by {
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
  }
```

你可以在这个练习中自己试试。

```lean
example (a b : ℝ) : a = b ↔ b - a = 0 := by {
  sorry
}
```

这是本文件的结尾，你学习了如何处理蕴含关系和等价关系。你学习了以下策略：
* `intro`
* `apply`
* `have`
* `constructor`
