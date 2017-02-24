namespace Dawg

module Graph = 

    /// Indicates unique id of a node.
    type Vertex = int

    type EdgeType =
        | Solid
        | Soft
        static member (==) (x, y) =
            match (x, y) with
                | (Solid, Solid) -> true
                | (Soft, Soft) -> true
                | (_, _) -> false

    /// Destination node, edge type.
    type Edge = Vertex * EdgeType

    /// Edge with its label.
    type LabeledEdge<'a> = 'a * Edge

    /// Edge with its startpoint.
    type RootedEdge<'a> = Vertex * 'a * Edge
    
    /// Node structure contains the node's id, suf binding (Nothing iff root) and the map of all outgoing edges.
    type Node<'a when 'a : comparison> = private {
        nodeId: Vertex;
        sufId: Vertex option;
        edges: Map<'a, Edge>;
    } with
        member this.NodeId = this.nodeId
        member this.SufId = this.sufId
        member this.Edges = this.edges

    /// Graph structure contains ids of its root and sink as well as the map of all nodes.
    type Dawg<'a when 'a : comparison> = private {
        rootId: Vertex;
        sinkId: Vertex;
        nodes: Map<Vertex, Node<'a>>;
    } with
        member this.RootId = this.rootId
        member this.SinkId = this.sinkId
        member this.Nodes = this.nodes

    type private Maybe() =
      member this.Bind(m, f) =
        match m with
            | Some v -> f v 
            | None -> None
      member this.Return(v) = Some v

    let private rootIx = 0

    let private maybe = Maybe()

    let private defaultNode = {
        nodeId = rootIx;
        sufId = None;
        edges = Map.empty;
    }

    /// Subword graph for an empty word.
    let private emptyGraph () = {
        rootId = rootIx;
        sinkId = rootIx;
        nodes = Map.ofList [(rootIx, defaultNode)]
    }

    let private isEdgeSolid (_, et) = et == Solid

    /// Returns node with a given index. Nothing iff such does not exist.
    let lookupNode ix g = Map.tryFind ix g.nodes

    /// Returns node with a given index. Error when such doesn't exist.
    let private getNode ix g =
        match lookupNode ix g with
            | Some n -> n
            | None -> failwith <| "there is no node with id: " + ix.ToString()

    /// Adds or updates an edge from a node with a given index in a given graph.
    let private setEdge ix c e g =
        let n = getNode ix g
        let n' = { n with edges = Map.add c e n.edges }
        { g with nodes = Map.add ix n' g.nodes }

    /// For a given graph returns its root node.
    let getRootNode g = getNode g.rootId g

    /// For a given graph returns its sink node.
    let getSinkNode g = getNode g.sinkId g

    let private getNodeSolidEdges n = List.filter (fun (_, edge) -> isEdgeSolid edge) (Map.toList n.edges)

    /// For a given node in a given graph returns its suf link node.
    let getSufNode n g = maybe {
        let! sid = n.sufId
        return (getNode sid g)
    }

    /// Adds node to a given graph.
    let private addNode n g =
        let k = n.nodeId
        { g with nodes = Map.add k n g.nodes }

    /// Returns number of edges for a given graph.
    let edgesNum g = Map.fold (fun s _ v -> s + v.edges.Count) 0 g.nodes

    /// Returns number of nodes for a given graph.
    let nodesNum g = g.nodes.Count

    /// Adds new node to a given graph. Returns new graph and new node's id.
    let private addNewNode g =
        let k = nodesNum g
        let n = { defaultNode with nodeId = k }
        (addNode n g, k)

    /// Performs fixing nodes in the suf bindings chain after inserting a new node. Function takes a predicate which
    /// indicates the end of fixing, node id where we need to redirect edges, edge type to redirect,
    /// starting node, edge label and a current graph.
    let rec private fixSufBindings edgePred redirectTo edgeType optW c g =
        match optW with
            | None -> (g, None)
            | Some w ->
                if edgePred w c then
                    (g, optW)
                else
                    let g' = setEdge w.nodeId c (redirectTo, edgeType) g
                    let w' = getSufNode w g' // from a new graph get vertex with (sufId w)
                    fixSufBindings edgePred redirectTo edgeType w' c g'

    /// Updates node with a given index in a graph with a new value.
    let private updateNode ix n g = { g with nodes = Map.add ix n g.nodes }

    /// Updates the suf binding of a node with a given id with a node represented by 'sufNode' value.
    let private changeSufNode g v sufNode =
        let vnode = getNode v g
        let vNodeNewSuf = 
            { vnode with
                sufId = maybe { 
                    let! suf = sufNode
                    return suf.nodeId
                }
            }
        updateNode v vNodeNewSuf g

    /// Updates the suf binding of a node with a given id of 'v'.
    let private changeSuf g v optSuf =
        match optSuf with
            | None -> changeSufNode g v None
            | Some suf -> changeSufNode g v <| Some (getNode suf g)

    /// Updates the suf binding of a graph's sink node with a given id.
    let private changeSinkSuf g suf = changeSuf g g.sinkId <| Some suf
    
    /// Looks up an edge from a given node with a given label.
    let findEdge n c = Map.tryFind c n.edges

    /// Returns an edge from a given node with a given label. Error when the specific edge does not exist.
    let private getEdge n c =
        match findEdge n c with
            | None -> failwith <| "there is no given egde from node with id: " + n.nodeId.ToString()
            | Some e -> e

    /// Checks whether an edge from a given node with a given label is solid. Error when such does not exist.
    let private isNodeEdgeSolid n c = isEdgeSolid <| getEdge n c

    /// Another necessary update of a graph after inserting a new node.
    /// Performs splitting given node in two after fixSufBindings to preserve correctness.
    /// For further details please visit: http://smurf.mimuw.edu.pl/node/581 (lecture in Polish, contains pseudocode).
    let private splitByNode g c optW =
        match optW with
            | None -> changeSinkSuf g g.rootId
            | Some w ->
                match getEdge w c with
                    | (v, Solid) -> changeSinkSuf g v
                    | (v, Soft) ->
                        let (g1, v') = addNewNode g
                        let redirectEdge g c (u, _) = setEdge v' c (u, Soft) g
                        let g2 = Map.fold redirectEdge g1 (getNode v g1).edges 
                        let g3 = setEdge w.nodeId c (v', Solid) g2
                        let g4 = changeSinkSuf g3 v'
                        let g5 = changeSufNode g4 v' (getSufNode (getNode v g4) g4)
                        let g6 = changeSuf g5 v (Some v')
                        let sufW = getSufNode w g6 // from a new graph get vertex with (sufId w)     
                        fst <| fixSufBindings isNodeEdgeSolid v' Soft sufW c g6

    /// Checks whether there is an edge from a given node with a given label.
    let private isEdge n c = (findEdge n c).IsSome

    /// Adds an element to a given graph creating a new graph for a word with this element appended.
    let insert g c =
        let (newSinkG, sinkNum) = addNewNode g
        let edgeToSink = (sinkNum, Solid)
        let oldSinkNum = g.sinkId
        let newSinkEdgeG = { setEdge oldSinkNum c edgeToSink newSinkG with sinkId = sinkNum }
        let w = getSufNode (getNode oldSinkNum newSinkEdgeG) newSinkEdgeG
        let (fixedG, fixedW) = fixSufBindings isEdge sinkNum Soft w c newSinkEdgeG
        splitByNode fixedG c fixedW    

    /// Constructs a subword graph for a given word. The performance of this function is linear
    /// in the length of a word.
    let construct w = Seq.fold insert (emptyGraph()) w

    /// Constructs a subword graph for a reversed word. The performance of this function is linear
    /// in the length of a word.
    let constructReversed w = construct <| Seq.rev w

    /// Finds the given word in the subword graph starting at the given node. Helper function for findNode.
    let private findNodeInternal (w:seq<'a>) (graph: Dawg<'a>) (node: Node<'a>) =
        use mutable it = w.GetEnumerator()
        let mutable res = Some node
        let mutable go = it.MoveNext()
        while go do
            let a = it.Current
            let node = res.Value
            if not <| isEdge node a then
                res <- None
                go <- false
            else
                let vertex, _ = getEdge node a
                res <- getNode vertex graph |> Some
                go <- it.MoveNext()
        res

    /// Finds the given word in the subword graph. On failure, returns Nothing. On success, returns the
    /// node in the subword graph at which the word ends. Performance is linear in the length of the word.
    let findNode word graph = findNodeInternal word graph (getRootNode graph)

    /// Indicates whether the subword graph contains the given word. Performance is linear in the length of the word.
    let elem word graph = (findNode word graph).IsSome

    /// Helper function for toWord.
    let rec private toWordWithStack g nId visited =
        let f acc (letter, (vertex, _)) = acc @ toWordWithStack g vertex (letter::visited)
        if nId = g.sinkId then
            [visited]
        else
            List.fold f [] (getNodeSolidEdges (getNode nId g))
            
    /// Returns a word corresponding the given subword graph. Performance is linear in the length of the word.
    let toWord g = toWordWithStack g g.rootId [] |> Seq.head |> Seq.rev

    /// Helper function for topsort. It takes a graph, list of unprocessed nodes with indegree equal to 0,
    /// current result and a mapping: vertex -> current indegree.
    let rec private toporder g nds acc m =
        match nds with
            | [] -> acc
            | h::t -> 
                let f (m1, t1) _ (dst, _) =
                    let dg = match Map.tryFind dst m1 with None -> 0 | Some x -> x
                    let t2 = if dg = 1 then getNode dst g :: t1 else t1
                    let m2 = Map.add dst (dg - 1) m1
                    (m2, t2)

                let (m', t') = Map.fold f (m, t) h.edges
                toporder g t' (h::acc) m'

    /// For a given graph returns a mapping: vertex -> indegree. Performance is linear in the size of the graph.
    let private countInDegrees g =
        let nds = Map.toList g.nodes |> List.map snd
        let initmap = Map.ofList [ for a in nds -> (a.nodeId, 0) ]
        let inc mp v =
            match Map.tryFind v mp with
                | None -> mp
                | Some x -> Map.add v (x+1) mp
        let f acc nd = Map.fold (fun mp _ (dst, _) -> inc mp dst) acc nd.edges
        List.fold f initmap nds

    /// For a given graph returns the list of nodes in a topological order. Performance is linear in the size of the graph.
    let topsort g = countInDegrees g |> toporder g [getRootNode g] [] |> List.rev

    /// Folds the edges in a graph starting at a given node. Returns computed value, as well as a mapping:
    /// vertex -> computed value.
    let foldBackFromNode (f: LabeledEdge<'a> -> 'b -> 'b -> 'b) (acc: 'b) (g: Dawg<'a>) (n: Node<'a>) =
        let mutable st = Map.empty

        /// Process the node in a postorder fashion. Helper function for foldrFromNode.
        let rec postorderNode f acc g n =

            /// Helper function for postorderNode.
            let postorderGo f g initacc acc e =
                let _, (dst, ety) = e
                match Map.tryFind dst st with
                    | None ->
                        let v = getNode dst g |> postorderNode f initacc g
                        st <- Map.add dst v st
                        f e acc v
                    | Some v -> f e acc v

            List.fold (postorderGo f g acc) acc (Map.toList n.edges)

        let v = postorderNode f acc g n
        (v, st)

    /// Folds the edges in a graph, using post-order traversal. Transformer function takes an edge,
    /// current node's state and state along the edge. Init state at node is equal to the accumulator.
    let foldBack (f: LabeledEdge<'a> -> 'b -> 'b -> 'b) (acc: 'b) (g: Dawg<'a>) =
        getRootNode g |> foldBackFromNode f acc g |> fst

    /// Returns the list of all subwords present in a given subword graph.
    let subwords g =
        foldBack 
            (fun (c, _) s1 s2 -> 
                let sc = seq { yield c; }
                seq {
                    yield! s1;
                    yield sc;
                    yield! Seq.map (fun l -> Seq.append sc l) s2
                }
            )
            Seq.empty
            g

    /// Returns the number of all subwords present in the given subword graph.
    /// Performance is linear in the size of the graph.
    let subwordsNum g = foldBack (fun _ s1 s2 -> 1 + s1 + s2) 0 g

    /// Folds the edges in a graph up to a given node. Returns computed value, as well as a mapping:
    /// vertex -> computed value.
    let foldToNode (f: 'b -> 'b -> RootedEdge<'a> -> 'b) (acc: 'b) (g: Dawg<'a>) (n: Node<'a>) =
        let mutable st = Map.empty

        /// Helper function for foldlToNode. It takes a transformer function, accumulator, a subword graph
        /// a node up to which we want to continue folding and a list of unprocessed nodes in a topological order.
        let rec toporderNode
            (f: 'b -> 'b -> RootedEdge<'a> -> 'b)
            (acc: 'b)
            (g: Dawg<'a>)
            (nto: Node<'a>)
            (nds: Node<'a> list) =

            /// Helper function for extracting node's state. It takes a default value which is returned in case of
            /// given vertex absence in the state.
            let getNodeState idx def =
                match Map.tryFind idx st with
                    | None -> def
                    | Some v -> v
                    
            match nds with
                | [] -> failwith "toporderNode: invalid end node"
                | h::t ->
                    if h.nodeId = nto.nodeId then
                        getNodeState nto.nodeId acc
                    else
                        let currId = h.nodeId
                        let go e =
                            let c, (dst, ety) = e
                            let v1 = getNodeState currId acc
                            let v2 = getNodeState dst acc
                            st <- Map.add dst (f v1 v2 (currId, c, (dst, ety))) st

                        Map.toList h.edges |> List.iter go
                        toporderNode f acc g nto t
                        
        let v = topsort g |> toporderNode f acc g n
        (v, st)

    /// Folds the edges in a graph, using topological order traversal. Transformer function takes current
    /// node's state, current state along the edge, an edge and it produces a new state along the edge.
    /// Init state at node is equal to the accumulator.
    let fold (f: 'b -> 'b -> RootedEdge<'a> -> 'b) (acc: 'b) (g: Dawg<'a>) =
        getSinkNode g |> foldToNode f acc g |> fst
