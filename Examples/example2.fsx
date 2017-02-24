// This module solves the following problem (in linear time):
// For a given pair of strings: A, B and a positive natural number K, calculate the number of
// subwords of A that occur in B exactly K times.
//
// input 1:
//  acb
//  abab
//  2
// output 1:
//  2
//
// input 2:
//  abc
//  abab
//  2
// output 2:
//  3
//
// In a solution we assume that neither '#' nor '$' occur in given strings.
//

#load "../Dawg/Dawg.fs"
open Dawg

module SG = Graph

let marker1 = '#'
let marker2 = '$'

/// Counts how many times does the given word occur in the given graph.
let countRepeats w g =
    let g' = SG.insert g marker1
    match SG.findNode w g' with
        | None -> 0
        | Some n ->           
            let f (_, (dst, _)) st1 st2 =
                if dst = g'.SinkId
                    then 1 + st1
                else st1 + st2
        
            SG.foldBackFromNode f 0 g' n |> fst

/// Brute force solution.
let bruteForce a b k =
    let ga = SG.construct a
    let gb = Seq.singleton(marker1) |> Seq.append b |> SG.construct
    let f acc w = if countRepeats w gb = k then acc + 1 else acc
    Seq.fold f 0 (SG.subwords ga)

/// Linear time solution.
let solve a b k =
    let amark = a + marker1.ToString()

    let w = amark + b + marker2.ToString()

    let g = SG.construct w
    let aend = match SG.findNode amark g with None -> failwith "no way!" | Some n -> n

    let f1 st1 st2 (src, _, _) = if src = g.RootId then st2 + 1 else st1 + st2
    
    let f3 dst st1 st2 =
        if dst = g.SinkId then 1 + st1
        else if dst = aend.NodeId then st1
        else st1 + st2

    let f2 (_, (dst, _)) st1 st2 = (fst st1 || fst st2 || dst = aend.NodeId, f3 dst (snd st1) (snd st2))

    // for each vertex it's number of associated subwords
    let ndsWordsNum = SG.getSinkNode g |> SG.foldToNode f1 0 g |> snd

    // for each vertex it's reachability of '#', and the number of ways to '$' but not through '#'
    let ndsRchblty = SG.foldBackFromNode f2 (false, 0) g (SG.getRootNode g) |> snd

    let f4 acc (nid, (hreach, dways)) =
        if hreach && (dways = k) then acc + (match Map.tryFind nid ndsWordsNum with None -> 0 | Some x -> x)
        else acc

    Map.toList ndsRchblty |> List.fold f4 0 

// Main
let sr = new System.IO.StreamReader(System.Console.OpenStandardInput())
let testsNum = sr.ReadLine() |> System.Int32.Parse
seq { while true do yield sr.ReadLine() }
    |> Seq.take testsNum
    |> Seq.iter
        ( fun ln ->
            let words = ln.Split(' ')
            let a = words.[0]
            let b = words.[1]
            let k = words.[2] |> System.Int32.Parse
            printfn "%d" (solve a b k)
        )