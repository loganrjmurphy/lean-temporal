import data.stream tactic
open tactic 

namespace LTL 

variable AP : Type

inductive formula 
| T : formula 
| atom : AP → formula 
| conj : formula → formula → formula 
| neg : formula → formula 
| next : formula → formula 
| until : formula → formula → formula 

local infix ` & ` : 70 := formula.conj
local notation ` ∼` Φ : 100:= formula.neg Φ 
local notation ` ●` Φ  : 100:= formula.next Φ 
local infixr ` 𝒰 ` : 80 := formula.until

namespace formula 

def disj (φ ψ : formula AP) :formula AP := 
∼ (∼φ & ∼ψ)

local infix ` + ` :60 := formula.disj _


def impl (φ ψ : formula AP) : formula AP:= 
∼φ + ψ

local infix ` ⇒` : 50 := formula.impl _

def bimpl (φ ψ : formula AP) : formula AP := 
φ ⇒ ψ & ψ ⇒ φ
local infix ` ⇔ ` : 50 := formula.bimpl _

def eventually (φ : formula AP) : formula AP := 
formula.T 𝒰 φ 
local notation ` ◆` : 100 := formula.eventually _

def always (φ : formula AP) : formula AP := 
∼◆∼φ
local notation ` ◾` : 100 :=formula.always _

def inf_word : Type := stream (set AP)

local notation σ[i..] := stream.drop i σ 

namespace sat 

def sat :  inf_word AP → formula AP → Prop 
| _  formula.T  :=  true 
| σ (formula.atom a) :=  a ∈ σ 0 
| σ (formula.conj φ ψ) :=  (sat σ φ) ∧ (sat σ ψ)
| σ (∼ φ)   :=  ¬ (sat σ φ)
| σ (● φ)   :=  sat (σ[1..]) φ 
| σ (φ 𝒰 ψ) :=  ∃ j, sat (σ[j..]) ψ  ∧ ∀ i, i < j → sat (σ[i..]) φ 

notation  σ ` ⊨ ` φ := sat _ σ φ 

def disj (φ ψ : formula AP) (σ : inf_word AP) : 
    (σ ⊨ φ + ψ) ↔ (σ ⊨ φ) ∨ (σ ⊨ ψ) := 
begin
     rw disj, repeat {rw sat},
     rw [not_and, not_not,imp_iff_not_or, not_not],
end  


def impl (φ ψ : formula AP) (σ : inf_word AP) : 
    (σ ⊨ φ ⇒ ψ) ↔ (σ ⊨ φ) → (σ ⊨ ψ) := 
by { rw [impl,disj, sat, imp_iff_not_or]}


def eventually (φ : formula AP) (σ : inf_word AP) : 
    (σ ⊨ ◆φ) ↔ ∃ j, σ[j..] ⊨ φ := 
begin
    rw eventually,
    rw sat, split,
    { rintros ⟨w,H1,H2⟩,
      use w, exact H1 },
    { rintros ⟨w,H⟩, use w,
      split, {exact H}, {intros, trivial}} 
end 

def always (φ : formula AP) (σ : inf_word AP)



end sat 

end formula





end LTL