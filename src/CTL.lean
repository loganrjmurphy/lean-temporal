import data.stream tactic
open stream tactic 

namespace CTL

variables AP : Type

mutual inductive state_formula, path_formula
with state_formula : Type
| T             : state_formula
| atom (a : AP) : state_formula
| conj (Φ₁ Φ₂ : state_formula ) : state_formula
| neg (Φ : state_formula) : state_formula
| E (φ : path_formula) : state_formula
| A (φ : path_formula) : state_formula
with path_formula : Type
| next (Φ : state_formula) : path_formula
| until (Φ₁ Φ₂ : state_formula) : path_formula
open state_formula
open path_formula

local notation  `∼` Φ := neg Φ
local notation Φ `and` Ψ := conj Φ Ψ
local notation `●` Φ := next Φ
local notation Φ `𝒰` Ψ := until Φ Ψ

structure TS :=
(S : Type)
(H : decidable_eq S)
(Act : Type)
(TR : set (S × Act × S))
(L  : S → set AP)

def Post_of  {M : TS AP} (s : M.S) (α : M.Act) : set (M.S) := {s' | (s,α,s') ∈ M.TR}

def Post {M : TS AP} (s : M.S) : set (M.S) :=
⋃ α : M.Act, Post_of _ s α

def fin_path {AP : Type} (M : TS AP) : Type := 
{l : list M.S // ∀ i : ℕ, }

def path {AP : Type} (M : TS AP) : Type := 
{s : stream M.S // ∀ i : ℕ, s (i + 1) ∈ Post _ (s i)}

def first {M : TS AP} (π : path  M) : M.S := π.val 0

def paths {AP : Type}
{M : TS AP} (s : M.S) : set (path M) :=
(λ π, s = (first _ π))

mutual def state_sat, path_sat {M : TS AP}
with state_sat : state_formula AP → M.S → Prop
| T := λ _, true
| (atom a) := λ s, a ∈ M.L s
| (Φ and Ψ) := λ s, state_sat Φ s ∧ state_sat Ψ s
| (∼ Φ) := λ s, ¬ (state_sat Φ s)
| (E φ) := λ s, ∃ π : path M, π ∈ paths s ∧ path_sat φ π
| (A φ) := λ s, ∀ π : path M, π ∈ paths s → path_sat φ π
with path_sat : path_formula AP → path M → Prop
| (● Φ) := λ π, state_sat Φ (π.val 1)
| (Φ 𝒰 Ψ) := λ π, 
 ∃ j, state_sat Ψ (π.val j) ∧ (∀ k < j, state_sat Φ (π.val k))

notation s `⊨ₛ` Φ := state_sat _ Φ s
notation π `⊨ₚ ` Φ := path_sat _ Φ π


def potentially (φ : state_formula AP) : state_formula AP := 
E(T 𝒰 φ)
notation `E◆` φ := potentially _ φ 

def inevitable (φ : state_formula AP) : state_formula AP := 
A(T 𝒰 φ)
notation `A◆` φ := inevitable _ φ 


def potentially_always (φ : state_formula AP) : state_formula AP := 
∼ (A◆(∼φ))
notation `E◾` φ := potentially_always _ φ 


def invariantly (φ : state_formula AP) : state_formula AP := 
∼ (E◆(∼φ))
notation `A◾` φ := invariantly _ φ 

namespace sat 

def potentially {AP : Type} {M : TS AP} (φ : state_formula AP) (s : M.S): 
(s ⊨ₛ φ) ↔ ∃ π ∈ paths s, ∃ j:ℕ, (subtype.val π j) ⊨ₛ φ := 
begin 
    split,
    intro s,
    
end 


end sat


end CTL