(* A randomized balanced binary tree structure. *)

namespace FsTreap

open System

type internal TreapNodeData<'k> =
  { key: 'k
  ; prio: Int32
  ; left: Treap<'k>
  ; right: Treap<'k>
  }

and Treap<'k> =
  internal
    | Leaf
    | Node of TreapNodeData<'k>

type Nearest<'k> =
  { lessmost: Option<'k>
  ; moremost: Option<'k>
  }

[<RequireQualifiedAccess>]
module Treap =

  let empty () =
    Leaf

  let singleton value =
    let gen = Random ()
    let prio = gen.Next ()
    Node { key = value; prio = prio; left = Leaf; right = Leaf }
  
  let internal rotateLeft treap =
    match treap with
      | Node { key = keyl; prio = priol; left = x; right =
          Node { key = keyr; prio = prior; left = y; right = z }
        } ->
        let left = Node { key = keyl; prio = priol; left = x; right = y }
        Node { key = keyr; prio = prior; left = left; right = z }
      | _ -> treap

  let internal rotateRight treap =
    match treap with
      | Node { key = keyr; prio = prior; right = z; left =
          Node { key = keyl; prio = priol; left = x; right = y }
        } ->
        let right = Node { key = keyr; prio = prior; left = y; right = z }
        Node { key = keyl; prio = priol; left = x; right = right }
      | _ -> treap

  let internal prioImplicit treap =
    match treap with
      | Leaf -> -1
      | Node { prio = prio } -> prio

  /// Rotate the tree in whatever way preserves the heap invariant.
  /// We assume that only one branch can be in violation of the heap
  /// invariant at a time, since this is what our normal treap algorithms
  /// do.
  let internal rotateHeap treap =
    match treap with
      | Leaf -> Leaf
      | Node { prio = prioHere; left = left; right = right } ->
        if prioImplicit left > prioHere then
          rotateRight treap
        else if prioImplicit right > prioHere then
          rotateLeft treap
        else
          treap
  
  /// Insert a value into the binary search tree and balance it.
  let insert value treap =
    let gen = Random ()
    let prio = gen.Next ()  // If we randomly generate heap priority, the tree balances.

    let rec insert' treap =
      match treap with
        | Leaf -> singleton value
        | Node ({ key = key; prio = prio; left = left; right = right } as data) ->
          rotateHeap <|
            if key > value then
              Node { data with left = insert' left }
            else if key < value then
              Node { data with right = insert' right }
            else
              treap

    insert' treap

  /// Construct a treap from a list.
  let ofList eles =
    List.fold (fun treap ele -> insert ele treap) (empty ()) eles

  /// Check if the given value is in the treap.
  let contains value treap =
    let rec contains' treap =
      match treap with
        | Leaf -> false
        | Node { key = key; left = left; right = right } ->
          if key > value then
            contains' left
          else if key < value then
            contains' right
          else
            true

    contains' treap

  /// Excise the given node from the treap.
  let rec internal chop treap =
    match treap with
      | Leaf -> Leaf
      | Node dataHere ->
        match dataHere with
          | { left = Leaf; right = Leaf } -> Leaf
          | { left = left; right = right } ->
            if prioImplicit left > prioImplicit right then
              match rotateRight <| Node dataHere with
                | Leaf -> Leaf  // Should never happen
                | Node data -> Node { data with right = chop data.right }
            else
              match rotateLeft <| Node dataHere with
                | Leaf -> Leaf  // Should never happen
                | Node data -> Node { data with left = chop data.left }

  /// Delete the node with the given key from the treap, if it exists.
  let delete value treap =
    // Frankly, I'm not really sure that this method actually keeps the
    // tree balanced. I think that we need to rotate the node up to the
    // root, then back down to the leaves.
    let rec delete' treap =
      match treap with
        | Leaf -> Leaf
        | Node data ->
          if data.key > value then
            Node { data with left = delete' data.left }
          else if data.key < value then
            Node { data with right = delete' data.right }
          else
            chop treap

    delete' treap

  /// Find the two nearest elements in the treap, if they exist. The nearest
  /// elements might be the element itself.
  let nearest value treap =
    let rec nearest' treap info =
      match treap with
        | Leaf -> info
        | Node { key = key; left = left; right = right } ->
          if key > value then
            nearest' left { info with moremost = Some key }
          else if key < value then
            nearest' right { info with lessmost = Some key }
          else
            { info with lessmost = Some key; moremost = Some key }

    nearest' treap { lessmost = None; moremost = None }
