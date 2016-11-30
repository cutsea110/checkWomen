module checkWomen where

open import Data.Bool
  renaming (Bool to 真理値; true to はい; false to いいえ; _∧_ to _&&_; _∨_ to _||_; not to !_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

infixl 0 _⇔_
_⇔_ : (P : Set) → (Q : Set) → Set
P ⇔ Q = (P → Q) × (Q → P)

data 出身 : Set where
  火星 : 出身
  金星 : 出身

data 性別 : Set where
  男 : 性別
  女 : 性別

data 人間 : Set where
  人 : 出身 → 性別 → 人間

data 質問 : Set where
  男か : 質問
  女か : 質問
  火星人か : 質問
  金星人か : 質問
  _かつ_ : 質問 → 質問 → 質問
  _または_ : 質問 → 質問 → 質問

評価 : 人間 → 質問 → 真理値
評価 (人 _ 男) 男か = はい
評価 (人 _ 女) 男か = いいえ
評価 (人 _ 男) 女か = いいえ
評価 (人 _ 女) 女か = はい
評価 (人 火星 _) 火星人か = はい
評価 (人 金星 _) 火星人か = いいえ
評価 (人 火星 _) 金星人か = いいえ
評価 (人 金星 _) 金星人か = はい
評価 h (q₁ かつ q₂) = (評価 h q₁) && 評価 h q₂
評価 h (q₁ または q₂) = (評価 h q₁) || (評価 h q₂)

_が女 : 人間 → Set
人 _ 男 が女 = ⊥
人 _ 女 が女 = ⊤
_が男 : 人間 → Set
人 _ 男 が男 = ⊤
人 _ 女 が男 = ⊥
_が火星人 : 人間 → Set
人 火星 _ が火星人 = ⊤
人 金星 _ が火星人 = ⊥
_が金星人 : 人間 → Set
人 火星 _ が金星人 = ⊥
人 金星 _ が金星人 = ⊤

_が金星人男 : 人間 → Set
h が金星人男 = h が金星人 × h が男

_が火星人女 : 人間 → Set
h が火星人女 = h が火星人 × h が女

_が金星人女 : 人間 → Set
h が金星人女 = h が金星人 × h が女

_が火星人男 : 人間 → Set
h が火星人男 = h が火星人 × h が男

data 正直者か嘘つき : 人間 → Set where
  正直者 : ∀ {h} → h が金星人男 ⊎ h が火星人女 → 正直者か嘘つき h
  嘘つき : ∀ {h} → h が火星人男 ⊎ h が金星人女 → 正直者か嘘つき h

判別 : (h : 人間) → 正直者か嘘つき h
判別 (人 火星 男) = 嘘つき (inj₁ (tt , tt))
判別 (人 火星 女) = 正直者 (inj₂ (tt , tt))
判別 (人 金星 男) = 正直者 (inj₁ (tt , tt))
判別 (人 金星 女) = 嘘つき (inj₂ (tt , tt))

_に対する_の回答 : 質問 → 人間 → 真理値
q に対する h の回答 with 判別 h
... | 正直者 x = 評価 h q
... | 嘘つき x = ! (評価 h q)

女性判別器 : ∃ λ (q : 質問) → ∀ (h : 人間) → q に対する h の回答 ≡ はい ⇔ h が女
女性判別器 = 火星人か , (λ h → はいと回答すれば女 h , 女ならはいと回答 h)
  where
    はいと回答すれば女 : ∀ h → 火星人か に対する h の回答 ≡ はい → h が女
    はいと回答すれば女 (人 火星 男) ()
    はいと回答すれば女 (人 火星 女) prf = tt
    はいと回答すれば女 (人 金星 男) ()
    はいと回答すれば女 (人 金星 女) prf = tt
    女ならはいと回答 : ∀ h → h が女 → 火星人か に対する h の回答 ≡ はい
    女ならはいと回答 (人 火星 男) ()
    女ならはいと回答 (人 火星 女) tt = refl
    女ならはいと回答 (人 金星 男) ()
    女ならはいと回答 (人 金星 女) tt = refl
