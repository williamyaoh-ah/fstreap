namespace FsTreap.Tests

module Treap =

  open System

  open Xunit

  open FsCheck
  open FsCheck.Xunit

  open FsTreap

  /// Check if the treap is a valid binary search tree.
  let satisfiesBtree treap =
    let rec satisfies' lessmost moremost treap =
      match treap with
        | Leaf -> true
        | Node { key = key; left = left; right = right } ->
          let satisfiesLeft =
            match lessmost with
              | None -> true
              | Some value -> key > value
          let satisfiesRight =
            match moremost with
              | None -> true
              | Some value -> key < value
          satisfiesLeft && satisfiesRight
            && satisfies' lessmost (Some key) left
            && satisfies' (Some key) moremost right

    satisfies' None None treap

  /// Check if the treap is a valid max heap.
  let satisfiesHeap treap =
    let rec satisfies' cap treap =
      match treap with
        | Leaf -> true
        | Node { prio = prio; left = left; right = right } ->
          prio <= cap
            && satisfies' prio left
            && satisfies' prio right

    satisfies' Int32.MaxValue treap

  /// Check if the treap is a valid treap.
  let satisfiesTreap treap =
    satisfiesBtree treap && satisfiesHeap treap

  let flip f x y =
    f y x

  /// Generate a treap based on a generator of elements that have comparison.
  let genTreap eleGen =
    Gen.listOf eleGen
      |> Gen.map (List.fold (flip Treap.insert) (Treap.empty ()))

  type Int32TreapArb () =
    static member Int32TreapArb () =
      genTreap Arb.generate<Int32>
        |> Arb.fromGen

  [<Fact>]
  let ``empty treap satisfies treap invariants`` () =
    let treap: Treap<Int32> = Treap.empty ()
    let result: Boolean = satisfiesTreap treap

    Assert.True result

  [<Property( MaxTest=5000 )>]
  let ``singleton treap satisfies treap invariants`` (value: Int32) =
    let treap = Treap.singleton value

    satisfiesTreap treap

  [<Property( MaxTest=1000, Arbitrary=[| typeof<Int32TreapArb> |] )>]
  let ``arbitrary treaps satisfy treap invariants`` (treap: Treap<Int32>) =
    satisfiesTreap treap
