namespace FsTreap.Tests

module Treap =

  open Xunit

  open FsCheck
  open FsCheck.Xunit

  open FsTreap

  [<Fact>]
  let ``1 + 1 = 3`` () =
    Assert.Equal (1 + 1, 3)