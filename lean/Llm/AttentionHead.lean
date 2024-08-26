import Llm.Attention
import Llm.DenseNoBias

structure AttentionHead (Dₖ D_emb: Nat) where
  q: DenseNoBias D_emb Dₖ
  k: DenseNoBias D_emb Dₖ
  v: DenseNoBias D_emb Dₖ

def AttentionHead.forward
  (self: AttentionHead Dₖ D_emb)
  (inp: Vector  T (Vector  D_emb Float))
: Vector T (Vector Dₖ Float ) :=
  let Q := self.q.forward inp
  let K := self.k.forward inp
  let V := self.v.forward inp
  attention_forward Q K V

def AttentionHead.forward_batched
  (self: AttentionHead Dₖ D_emb)
  (inp: Vector B (Vector T (Vector D_emb Float)))
: Vector B (Vector T (Vector Dₖ Float))  :=
  inp.map self.forward

def AttentionHead.backward
  (self: AttentionHead Dₖ D_emb)
  (inp: Vector T (Vector D_emb Float))
  (dout: Vector T (Vector Dₖ Float))
:
  -- gradients for attention head
  AttentionHead Dₖ D_emb ×
  -- dinp
  (Vector T (Vector D_emb Float) )
:=
    -- get the gradients of the key, query and value matrices
    let Q := self.q.forward inp
    let K := self.k.forward inp
    let V := self.v.forward inp

    let (dQ, dK,dV) := attention_backwards dout Q K V

    let (dq, dinp_q) := self.q.backward inp dQ
    let (dk, dinp_k) := self.k.backward inp dK
    let (dv, dinp_v) := self.v.backward inp dV

    let dinp := dinp_q + dinp_k + dinp_v

    ((AttentionHead.mk dq dk dv), dinp)


def AttentionHead.sum_gradients
  (gradients: Vector B (AttentionHead Dₖ D_emb))
: AttentionHead Dₖ D_emb :=
  let qs := gradients.map (·.q)
  let ks := gradients.map (·.k)
  let vs := gradients.map (·.v)
  let q := DenseNoBias.sum_gradients qs
  let k := DenseNoBias.sum_gradients ks
  let v := DenseNoBias.sum_gradients vs
  AttentionHead.mk q k v

def AttentionHead.backward_batched
  (self: AttentionHead Dₖ D_emb)
  (inp: Vector B (Vector T (Vector D_emb Float)))
  (dout: Vector B (Vector T (Vector Dₖ Float)))
:
  -- gradients for attention head
  AttentionHead Dₖ D_emb ×
  -- dinp
  (Vector B (Vector T (Vector D_emb Float) ))
:=
  let backward_results := (inp.zip dout).map (fun (inp_i, dout_i) => self.backward inp_i dout_i)

  let att_gradients := backward_results.map (·.fst)
  let dinps := backward_results.map (·.snd)

  let att_gradients_sum := AttentionHead.sum_gradients att_gradients

  (att_gradients_sum, dinps)
