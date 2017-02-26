open Dawg
open System
open FsCheck


/// List of all nonempty sublists of a given list.
let sublists l =
    let n = List.length l
    seq { 
        for i in 0 .. n - 1 do
            for j in 0 .. n - i -> 
                let seqs = Seq.take j <| Seq.skip i l
                Seq.toList seqs 
    }
    |> Seq.distinct
    |> Seq.filter (fun s -> Seq.length s > 0)
    |> Seq.toList

let charSeq2String (s: char seq) = String.Concat s

let isInfixOf (a: string) (b: string) = b.IndexOf a >= 0

type MyStr = MyStr of string with
    member x.Get = match x with MyStr r -> r
    override x.ToString() = x.Get

let myStrGen =
    Gen.elements ['a'..'z'] 
    |> Gen.listOf 
    |> Gen.map (System.String.Concat >> MyStr)

type MyGenerators =
    static member MyStr () = Arb.fromGen myStrGen

type SubwordGraphProperties = 

    /// Test whether an empty string is a substring of a given string.
    static member prop_ElemEmpty1 (w: MyStr) = Graph.elem "" (Graph.construct w.Get)

    /// Test whether an empty word is a subword of a given word over integers.
    static member prop_ElemEmpty2 (w: int list) = Graph.elem [] (Graph.construct w)

    /// Test whether a string is its own substring.
    static member prop_ElemWord1 (w: MyStr) = let w' = w.Get in Graph.elem w' (Graph.construct w')

    /// Test whether a word over integers is its own subword.
    static member prop_ElemWord2 (w:int list) = Graph.elem w (Graph.construct w)

    /// Test elem function.
    static member prop_Elem (a: MyStr) (b: MyStr) =
        let a = a.Get
        let b = b.Get
        Graph.elem a (Graph.construct b) = isInfixOf a b

    /// Test subwords function.
    static member prop_Subwords (w: MyStr) =
        let w = w.Get
        let stringList = [for c in w -> c]
        let l1 = Graph.subwords (Graph.construct w) |> Seq.map Seq.toList |> Seq.toList
        let l2 = sublists stringList
        List.sort l1 = List.sort l2

    /// Test subwordsNum function.
    static member prop_SubwordsNum (w: MyStr) =
        let w = w.Get
        let stringList = [for c in w -> c]
        Graph.subwordsNum (Graph.construct w) = List.length (sublists stringList)

    /// Test insert function.
    static member prop_Insert (w: int list) (a: int) =
        Graph.construct (w @ [a]) = Graph.insert (Graph.construct w) a

    /// Test word extraction from a graph.
    static member prop_ConstrToWord (w: MyStr) = charSeq2String (Graph.toWord (Graph.construct w.Get)) = w.Get

    /// Test linear number of nodes. Implication below is a simple theorem.
    static member prop_NodesNum (w: MyStr) =
        let w = w.Get
        let g = Graph.construct w
        let n = w.Length
        let v = Graph.nodesNum g
        n >= 3 ==> (v <= 2 * n - 1)

    /// Test linear number of edges. Implication below is a simple theorem.
    static member prop_EdgesNum (w: MyStr) = 
        let w = w.Get
        let g = Graph.construct w
        let n = w.Length
        let e = Graph.edgesNum g
        n >= 3 ==> (e <= 3 * n - 4)


[<EntryPoint>]
let main argv =
    Arb.register<MyGenerators> () |> ignore
    Check.QuickAll<SubwordGraphProperties> ()
    0
