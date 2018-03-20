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

  /// Basic binary search tree insert. Does not do any rebalancing.
  let insertb value treap =
    let rec insertb' treap =
      match treap with
        | Leaf -> Treap.singleton value
        | Node data ->
          if data.key > value then
            Node { data with left = insertb' data.left }
          else if data.key < value then
            Node { data with right = insertb' data.right }
          else
            treap

    insertb' treap

  let flip f x y =
    f y x
  
  /// Generate a treap based on a generator of elements that have comparison.
  let genTreap eleGen =
    Gen.listOf eleGen
      |> Gen.map (List.fold (flip Treap.insert) (Treap.empty ()))

  /// Generate a naive binary search tree, without rebalancing.
  let genBTree eleGen =
    Gen.listOf eleGen
      |> Gen.map (List.fold (flip insertb) (Treap.empty ()))

  type Int32TreapArb () =
    static member Int32TreapArb () =
      genTreap Arb.generate<Int32>
        |> Arb.fromGen

  type Int32BTreeArb () =
    static member Int32BTreeArb () =
      genBTree Arb.generate<Int32>
        |> Arb.fromGen

  [<Fact>]
  let ``empty treap satisfies treap invariants`` () =
    let treap: Treap<Int32> = Treap.empty ()
    let result: Boolean = satisfiesTreap treap

    Assert.True result

  [<Fact>]
  let ``empty treap is empty`` () =
    let treap: Treap<Int32> = Treap.empty ()
    let result: Boolean = Treap.isEmpty treap

    Assert.True result

  [<Fact>]
  let ``empty treap has count 0`` () =
    let treap: Treap<Int32> = Treap.empty ()
    let count = Treap.count treap

    Assert.Equal(0, count)

  [<Fact>]
  let ``empty treap is isomorphic to empty list`` () =
    let treap: Treap<Int32> = Treap.empty ()
    let l = Treap.toList treap
    let result: Boolean = l = []

    Assert.True result

  [<Property( MaxTest=5000 )>]
  let ``singleton treap is not empty`` (value: Int32) =
    let treap = Treap.singleton value
    let result: Boolean = not <| Treap.isEmpty treap

    result

  [<Property( MaxTest=5000 )>]
  let ``singleton treap has count 1`` (value: Int32) =
    let treap = Treap.singleton value
    let count = Treap.count treap

    count = 1

  [<Property( MaxTest=5000 )>]
  let ``singleton treap is isomorphic to singleton list`` (value: Int32) =
    let treap = Treap.singleton value
    let l = Treap.toList treap

    l = [value]
    
  [<Property( MaxTest=5000 )>]
  let ``singleton treap satisfies treap invariants`` (value: Int32) =
    let treap = Treap.singleton value

    satisfiesTreap treap

  [<Property( MaxTest=5000, EndSize=1000, Arbitrary=[| typeof<Int32BTreeArb> |] )>]
  let ``naive btree satisfies btree invariants`` (treap: Treap<Int32>) =
    satisfiesBtree treap
  
  [<Property( MaxTest=5000, EndSize=1000, Arbitrary=[| typeof<Int32BTreeArb> |] )>]
  let ``left rotates always preserve search tree invariants`` (treap: Treap<Int32>) =
    satisfiesBtree treap && satisfiesBtree <| Treap.rotateLeft treap    

  [<Property( MaxTest=5000, EndSize=1000, Arbitrary=[| typeof<Int32BTreeArb> |] )>]
  let ``right rotates always preserve search tree invariants`` (treap: Treap<Int32>) =
    satisfiesBtree treap && satisfiesBtree <| Treap.rotateRight treap

  [<Property( MaxTest=5000, EndSize=1000, Arbitrary=[| typeof<Int32BTreeArb> |] )>]
  let ``rotateHeap always preserves search tree invariants`` (treap: Treap<Int32>) =
    satisfiesBtree treap && satisfiesBtree <| Treap.rotateHeap treap

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``arbitrary treaps satisfy treap invariants`` (eles: List<Int32>) =
    let treap = Treap.ofList eles

    satisfiesTreap treap

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``inserting preserves treap invariants`` (eles: List<Int32>) (ele: Int32) =
    let treap = Treap.ofList eles

    satisfiesTreap <| Treap.insert ele treap

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``inserted element can be found`` (eles: List<Int32>) (ele: Int32) =
    let treap = Treap.ofList eles

    Treap.contains ele <| Treap.insert ele treap

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``inserting an element leaves other elements unchanged`` (eles: List<Int32>) (ele: Int32) =
    let treap = Treap.ofList eles
    let treap = Treap.insert ele treap

    List.forall (fun ele -> Treap.contains ele treap) eles        

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``all elements can be found in constructed treap`` (eles: List<Int32>) =
    let treap = Treap.ofList eles

    List.forall (fun ele -> Treap.contains ele treap) eles

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``deleting an element causes lack of contain`` (eles: List<Int32>) (ele: Int32) =
    let treap = Treap.ofList <| ele::eles

    not (Treap.contains ele <| Treap.delete ele treap)

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``deleting an element leaves other elements unchanged`` (eles: List<Int32>) (ele: Int32) =
    let treap = Treap.ofList <| ele::eles
    let treap = Treap.delete ele treap

    eles
      |> List.filter (fun x -> x <> ele)
      |> List.forall (fun ele -> Treap.contains ele treap)

  type Operation = Insert | Delete

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``arbitrary sequence of inserts and deletes preserves invariants``
    (eles: List<(Int32 * Operation)>) =

    let treap =
      List.fold (fun treap (ele, operation) ->
                  match operation with
                    | Insert -> Treap.insert ele treap
                    | Delete -> Treap.delete ele treap)
        (Treap.empty ())
        eles

    satisfiesTreap treap

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``nearest always produces elements in treap`` (eles: List<Int32>) (ele: Int32) =
    let treap = Treap.ofList eles
    let { lessmost = lessmost; moremost = moremost } = Treap.nearest ele treap

    (match lessmost with
      | None -> true
      | Some ele -> Treap.contains ele treap) &&
    (match moremost with
      | None -> true
      | Some ele -> Treap.contains ele treap)

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``nearest actually produces bounds on value`` (eles: List<Int32>) (ele: Int32) =
    let treap = Treap.ofList eles
    let { lessmost = lessmost; moremost = moremost } = Treap.nearest ele treap

    let max treap =
      let rec max' treap max =
        match treap with
          | Leaf -> max
          | Node { key = key; right = right } ->
            max' right key

      max' treap Int32.MinValue

    let min treap =
      let rec min' treap min =
        match treap with
          | Leaf -> min
          | Node { key = key; left = left } ->
            min' left key

      min' treap Int32.MaxValue

    match treap with
      | Leaf -> lessmost = None && moremost = None
      | Node _ ->
        let (min, max) = (min treap, max treap)
        (match lessmost with
          | None -> ele <= min
          | Some value -> ele >= value) &&
        (match moremost with
          | None -> ele >= max
          | Some value -> ele <= value) 

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``toList always produces elements in treap`` (eles: List<Int32>) =
    let treap = Treap.ofList eles
    let l = Treap.toList treap

    List.forall (fun ele -> Treap.contains ele treap) l

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``toList always produces elements in sorted order`` (eles: List<Int32>) =
    let treap = Treap.ofList eles
    let l = Treap.toList treap

    let isSorted l =
      let rec isSorted' l last =
        match (l, last) with
          | ([], _) -> true
          | (h::t, None) -> isSorted' t (Some h)
          | (h::t, Some last) -> h >= last && isSorted' t (Some h)

      isSorted' l None

    isSorted l

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``count and toList always agree`` (eles: List<Int32>) =
    let treap = Treap.ofList eles

    Treap.count treap = List.length (Treap.toList treap)

  [<Property( MaxTest=1000, EndSize=1000 )>]
  let ``count and isEmpty always agree`` (eles: List<Int32>) =
    let treap = Treap.ofList eles
    let count = Treap.count treap

    match Treap.isEmpty treap with
      | true -> count = 0
      | false -> count > 0