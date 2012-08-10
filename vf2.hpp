#ifndef VF2_H_
#define VF2_H_

#include <stdio.h>
#include <iostream>

#include <vector>
#include <utility>
#include <boost/graph/graph_traits.hpp>

#define BR asm("int $3;")

namespace graph_alg
{
    typedef int VIndex;
    typedef int EIndex;
    
    const VIndex NULL_VINDEX = -1;
    const EIndex NULL_EINDEX = -1;

    ///////////////////////////////////////////////////////////////////////
    //              class IsoMap
    // --------------------------------------------------------------------

    template<class G, class D>
    struct IsoMap
    {
	std::vector<VIndex> v_core;
	std::vector<EIndex> e_core;
	const G& graph;
	const D& dm;
	IsoMap(const G& g, const D& d)
	    :v_core(num_vertices(g), NULL_VINDEX),
	     e_core(num_edges(g), NULL_EINDEX),
	     graph(g), dm(d)
	    {}
    };

    
    template<class G, class D>
    std::ostream& print(std::ostream& stream,
			const IsoMap<G,D>& m1,
			const IsoMap<G,D>& m2, int n1)
    {
	int n2 = n1 == 1 ? 2 : 1;

	stream << "V_" << n1 << ":      ";
	for (unsigned int i = 0; i < m1.v_core.size(); ++i) {
	    stream.width(4); stream << i;
	}
	stream << std::endl;

	stream << "V_"<<n1<<"_to_"<<n2<<": ";
	for (unsigned int i = 0; i < m1.v_core.size(); ++i) {
	    stream.width(4); stream << m1.v_core[i];
	}
	stream << std::endl;

	stream << "E_"<<n1<<":      ";	
	for (unsigned int i = 0; i < m1.e_core.size(); ++i) {
	    stream.width(4);
	    stream << i << m1.dm.get_edge_descriptor(i);
	}
	stream << std::endl;

	stream << "E_"<<n1<<"_to_"<<n2<<": ";
	for (unsigned int i = 0; i < m1.e_core.size(); ++i) {
	    stream.width(4);
	    EIndex ei = m1.e_core[i];
	    if (ei != NULL_EINDEX)
		stream << ei << m2.dm.get_edge_descriptor(ei);
	}
	stream << std::endl;
	stream << std::endl;
	stream.width(0);
	return stream;
    }


    namespace detail
    {
        ///////////////////////////////////////////////////////////////////////
	template<class G>
	bool
	find_edge(
	    typename boost::graph_traits<G>::vertex_descriptor v_src,
	    typename boost::graph_traits<G>::vertex_descriptor v_trg,
	    const G& g,
	    typename boost::graph_traits<G>::edge_descriptor& e)
	{
	    using namespace boost;
	    typedef typename boost::graph_traits<G>::vertex_descriptor V;
	    typename boost::graph_traits<G>::out_edge_iterator i, iend;
	    for (tie(i,iend) = out_edges(v_src, g); i != iend; ++i)
	    {
		V v = target(*i, g);
		if (v == v_trg)
		{
		    e = *i;
		    return true;
		}
	    }
	    return false;
	}

        ///////////////////////////////////////////////////////////////////////
        //              class IndexIterator
        // --------------------------------------------------------------------
        class IndexIterator
        {
            const std::vector<VIndex>* pcore;
            const std::vector<int>*    pterm;
            VIndex current;
            
            void find_next()
                {
		    int n = pcore->size();
                    while (current < n)
                    {
                        if (pterm ?
                            (*pcore)[current] == NULL_VINDEX && (*pterm)[current] :
                            (*pcore)[current] == NULL_VINDEX)
                        {
                            return;
                        }
                        ++current;
                    }
                    current = NULL_VINDEX;
                }
        public:
            IndexIterator(const std::vector<VIndex>* pc = 0,
                          const std::vector<int>* pt = 0)
                : pcore(pc), pterm(pt), current(0)
                {
                    if (pc) 
                        find_next();
                    else
                        current = NULL_VINDEX;
                }

            EIndex get_v() const { return current; }
            void next()          { ++current; find_next(); }
        };

        typedef std::pair<IndexIterator,IndexIterator> IndexIteratorPair;

        ///////////////////////////////////////////////////////////////////////
        //              class MatchingPolicy
        // --------------------------------------------------------------------
        template<class G>
        struct GGIsomorphismPolicy
	{
	    static const bool chk_exit = true;

	    static bool check_term_count(int termout1, int termout2,
                                         int termin1, int termin2,
                                         int new1, int new2)
                {
                    return
                        termout1 == termout2 &&
                        termin1 == termin2 &&
                        new1 == new2;
                }

            // used with is_dead()
            static bool op(int v1, int v2) { return v1 != v2; }
	};


        template<class G>
        struct GSGIsomorphismPolicy
	{
	    static const bool chk_exit = false;

	    static bool check_term_count(int termout1, int termout2,
                                         int termin1, int termin2,
                                         int new1, int new2)
                {
                    return
                        termout1 >= termout2 &&
                        termin1 >= termin2 &&
                        new1 >= new2;
                }

            // used with is_dead()
            static bool op(int v1, int v2) { return v1 < v2; }
	};

	typedef std::pair<EIndex,EIndex> EIndexPair;
	typedef std::list<EIndexPair> EIndexPairs;
 
	struct M { std::vector<EIndex>& m; M(std::vector<EIndex>& m_) :m(m_) {} };

	struct MM1 : public M {
	    MM1(std::vector<EIndex>& m_) :M(m_) {}	    
	    void operator() (const EIndexPair& v) { m[v.first] = v.second; }
	};

	struct MM2 : public M {
	    MM2(std::vector<EIndex>& m_) :M(m_) {}	    
	    void operator() (const EIndexPair& v) { m[v.second] = v.first; }
	};


	struct M1 : public M {
	    M1(std::vector<EIndex>& m_) :M(m_) {}	    
	    void operator() (const EIndexPair& v) { m[v.first] = NULL_EINDEX; }
	};

	struct M2 : public M {
	    M2(std::vector<EIndex>& m_) :M(m_) {}	    
	    void operator() (const EIndexPair& v) { m[v.second] = NULL_EINDEX; }
	};
	

        ///////////////////////////////////////////////////////////////////////
        //              class DirectionPolicy
        // --------------------------------------------------------------------
	template<class G, class D>
	struct DirectedPolicy
	{
	    typedef G Graph;
	    typedef D DM;
            typedef typename boost::graph_traits<G>::vertex_descriptor VDescr;
            typedef typename boost::graph_traits<G>::edge_descriptor EDescr;

	    struct TCount
	    {
		int t_ou_len;
		int t_in_len;
		TCount() :t_ou_len(0), t_in_len(0) {}
		
		// used with is_dead()
                template<class OP>
                static bool cmp(const TCount& l1, const TCount& l2, OP op)
                    {
                        return
                            op(l1.t_len_out, l2.t_len_out) ||
                            op(l1.t_len_in, l2.t_len_in);
                    }
	    };

	    struct TArray : public IsoMap<G,D>
	    {
		std::vector<int> t_ou;
		std::vector<int> t_in;
		TArray(const G& g, const D& d)
		    :IsoMap<G,D>(g, d),
		     t_ou(num_vertices(g), 0),
		     t_in(num_vertices(g), 0)
		    {}

		static IndexIteratorPair get_pairs(const TArray*, const TCount&,
						   const TArray*, const TCount&);

		template<class EC>
		static bool feasible(VDescr v_g1, VDescr v_g2,
				     const TArray* t1, const TArray* t2,
				     int* termout, int* termin, int* nnew,
				     EIndexPairs*,
				     const EC&,
				     bool);

		void make_tarray(VIndex vi_g1, TCount*cnt, int depth);
		void backtrack_tarray(VIndex vi_last, int depth);
	    };
	};
	

	template<class G, class D>	
	IndexIteratorPair
	DirectedPolicy<G,D>::TArray::get_pairs(const TArray* tarr1, const TCount& cnt1,
					       const TArray* tarr2, const TCount& cnt2)
	{
            if (cnt1.t_ou_len > 0 && cnt2.t_ou_len > 0)
                return IndexIteratorPair(IndexIterator(&tarr1->v_core, &tarr1->t_ou),
                                         IndexIterator(&tarr2->v_core, &tarr2->t_ou));
	    
            if (cnt1.t_ou_len + cnt2.t_ou_len == 0 &&
		cnt1.t_in_len > 0 && cnt2.t_in_len > 0)
                return IndexIteratorPair(IndexIterator(&tarr1->v_core, &tarr1->t_in),
                                         IndexIterator(&tarr2->v_core, &tarr2->t_in));
	    
            if (cnt1.t_ou_len + cnt2.t_ou_len + cnt1.t_in_len + cnt2.t_in_len == 0)
                return IndexIteratorPair(IndexIterator(&tarr1->v_core),
                                         IndexIterator(&tarr2->v_core));	    
	    return IndexIteratorPair();
	}


	template<class G, class D>
	template<class EC>
	bool
	DirectedPolicy<G,D>::TArray::feasible(VDescr v_g1, VDescr v_g2,
					      const TArray* t1, const TArray* t2,
					      int* termout, int* termin, int* nnew,
					      EIndexPairs* added_edges,
					      const EC& ec,
					      bool exit_if_no_edge)
	{
	    const G& g1 = t1->graph;
	    const G& g2 = t2->graph;
	    const DM& dm1 = t1->dm;
	    const DM& dm2 = t2->dm;

	    // =======================================================
	    // check adjacent vertices of the v_g1 (OUT edges)
	    // =======================================================
	    typename boost::graph_traits<G>::out_edge_iterator o_i, o_end;
	    for (boost::tie(o_i,o_end) = out_edges(v_g1, g1); o_i != o_end; ++o_i)
	    {
		EDescr e_g1 = *o_i;
		EIndex ei_g1 = dm1.get_edge_index(e_g1);
		VDescr v_g1_adj = target(e_g1, g1);
		VIndex vi_g1_adj = dm1.get_vertex_index(v_g1_adj);
		if (t1->v_core[vi_g1_adj] != NULL_VINDEX)
		{
		    VIndex vi_g2_adj = t1->v_core[vi_g1_adj];
		    VDescr v_g2_adj = dm2.get_vertex_descriptor(vi_g2_adj);
		    
		    // if exist the edge (v_g2 -> v_g2_adj)
		    EDescr e_g2;
		    if (find_edge(v_g2, v_g2_adj, g2, e_g2) && ec(g1, g2, e_g1, e_g2))
		    {
			if (added_edges)
			{
			    EIndex ei_g2 = dm2.get_edge_index(e_g2);
			    added_edges->push_back(EIndexPair(ei_g2,ei_g1));
			}
		    }
		    else
			if (exit_if_no_edge)
			    return false;
		}
		else
		{
		    if (t1->t_ou[vi_g1_adj]) ++*termout;
		    if (t1->t_in[vi_g1_adj]) ++*termin;
		    if (!t1->t_ou[vi_g1_adj] && !t1->t_in[vi_g1_adj]) ++*nnew;
		}
	    }


	    // =======================================================
	    // check adjacent vertices of the v_g1 (IN edges)
	    // =======================================================
	    typename boost::graph_traits<G>::in_edge_iterator i_i, i_end;
	    for (boost::tie(i_i,i_end) = in_edges(v_g1, g1); i_i != i_end; ++i_i)
	    {
		EDescr e_g1 = *i_i;
		EIndex ei_g1 = dm1.get_edge_index(e_g1);
		VDescr v_g1_adj = source(e_g1, g1);
		VIndex vi_g1_adj = dm1.get_vertex_index(v_g1_adj);
		if (t1->v_core[vi_g1_adj] != NULL_VINDEX)
		{
		    VIndex vi_g2_adj = t1->v_core[vi_g1_adj];
		    VDescr v_g2_adj = dm2.get_vertex_descriptor(vi_g2_adj);
		    
		    // if exist the edge (v_g2_adj -> v_g2)
		    EDescr e_g2;
		    if (find_edge(v_g2_adj, v_g2, g2, e_g2) && ec(g1, g2, e_g1, e_g2))
		    {
			if (added_edges)
			{
			    EIndex ei_g2 = dm2.get_edge_index(e_g2);
			    added_edges->push_back(EIndexPair(ei_g2,ei_g1));
			}
		    }
		    else
			if (exit_if_no_edge)
			    return false;
		}
		else
		{
		    if (t1->t_ou[vi_g1_adj]) ++*termout;
		    if (t1->t_in[vi_g1_adj]) ++*termin;
		    if (!t1->t_ou[vi_g1_adj] && !t1->t_in[vi_g1_adj]) ++*nnew;
		}
	    }

	    return true;
	}


	template<class G, class D>
	void DirectedPolicy<G,D>::TArray::make_tarray(VIndex vi_g1, TCount*cnt, int depth)
	{
	    const G& g = this->graph;
	    const DM& dm = this->dm;

	    if (t_ou[vi_g1] == 0) t_ou[vi_g1] = depth; else --cnt->t_ou_len;
	    if (t_in[vi_g1] == 0) t_in[vi_g1] = depth; else --cnt->t_in_len;
	    
	    VDescr v = dm.get_vertex_descriptor(vi_g1);

	    typename boost::graph_traits<G>::out_edge_iterator o_i, o_end;
	    for (boost::tie(o_i,o_end) = out_edges(v, g); o_i != o_end; ++o_i)
	    {
		VIndex vi_adj = dm.get_vertex_index(target(*o_i, g));
		if (t_ou[vi_adj] == 0)
		{
		    t_ou[vi_adj] = depth;
		    ++cnt->t_ou_len;
		}
	    }

	    typename boost::graph_traits<G>::in_edge_iterator i_i, i_end;
	    for (boost::tie(i_i,i_end) = in_edges(v, g); i_i != i_end; ++i_i)
	    {
		VIndex vi_adj = dm.get_vertex_index(source(*i_i, g));
		if (t_in[vi_adj] == 0)
		{
		    t_in[vi_adj] = depth;
		    ++cnt->t_in_len;
		}
	    }
	   
	}


	template<class G, class D>
	void DirectedPolicy<G,D>::TArray::backtrack_tarray(VIndex vi_last, int depth)
	{
	    if (t_ou[vi_last] == depth) t_ou[vi_last] = 0;
	    if (t_in[vi_last] == depth) t_in[vi_last] = 0;

	    VDescr v = this->dm.get_vertex_descriptor(vi_last);

	    typename boost::graph_traits<G>::out_edge_iterator o_i, o_end;
	    for (boost::tie(o_i,o_end) = out_edges(v, this->graph); o_i != o_end; ++o_i)
	    {
		VIndex vi_adj = this->dm.get_vertex_index(target(*o_i, this->graph));
		if (t_ou[vi_adj] == depth) t_ou[vi_adj] = 0;
	    }

	    typename boost::graph_traits<G>::in_edge_iterator i_i, i_end;
	    for (boost::tie(i_i,i_end) = in_edges(v, this->graph); i_i != i_end; ++i_i)
	    {
		VIndex vi_adj = this->dm.get_vertex_index(source(*i_i, this->graph));
		if (t_in[vi_adj] == depth) t_in[vi_adj] = 0;
	    }
	}


        ///////////////////////////////////////////////////////////////////////
        //              class UnDirectionPolicy
        // --------------------------------------------------------------------
	template<class G, class D>
	struct UnDirectedPolicy
	{
	    typedef G Graph;
	    typedef D DM;
            typedef typename boost::graph_traits<G>::vertex_descriptor VDescr;
            typedef typename boost::graph_traits<G>::edge_descriptor EDescr;

	    struct TCount
	    {
		int t_len;
		TCount() :t_len(0) {}
		// used with is_dead()
                template<class OP>
                static bool cmp(const TCount& l1, const TCount& l2, OP op)
                    {
                        return op(l1.t_len, l2.t_len);
                    }
	    };

	    struct TArray : public IsoMap<G,D>
	    {
		std::vector<int> t;
		TArray(const G& g, const D& d)
		    :IsoMap<G,D>(g, d),
		     t(num_vertices(g), 0)
		    {}

		static IndexIteratorPair get_pairs(const TArray*, const TCount&,
						   const TArray*, const TCount&);

		template<class EC>
		static bool feasible(VDescr v_g1, VDescr v_g2,
				     const TArray* t1, const TArray* t2,
				     int* termout, int* termin, int* nnew,
				     EIndexPairs*,
				     const EC&,
				     bool);

		void make_tarray(VIndex vi_g1, TCount*cnt, int depth);
		void backtrack_tarray(VIndex vi_last, int depth);
	    };
	};



	template<class G, class D>	
	IndexIteratorPair
	UnDirectedPolicy<G,D>::TArray::get_pairs(const TArray* tarr1, const TCount& cnt1,
						 const TArray* tarr2, const TCount& cnt2)
	{
            if (cnt1.t_len > 0 && cnt2.t_len > 0)
                return IndexIteratorPair(IndexIterator(&tarr1->v_core, &tarr1->t),
                                         IndexIterator(&tarr2->v_core, &tarr2->t));   
            if (cnt1.t_len + cnt2.t_len == 0)
                return IndexIteratorPair(IndexIterator(&tarr1->v_core),
                                         IndexIterator(&tarr2->v_core));
	    return IndexIteratorPair();
	}


	template<class G, class D>
	template<class EC>
	bool
	UnDirectedPolicy<G,D>::TArray::feasible(VDescr v_g1, VDescr v_g2,
						const TArray* t1, const TArray* t2,
						int* termout, int* termin, int* nnew,
						EIndexPairs* added_edges,
						const EC& ec,
						bool exit_if_no_edge)
	{
	    const G& g1 = t1->graph;
	    const G& g2 = t2->graph;
	    const DM& dm1 = t1->dm;
	    const DM& dm2 = t2->dm;

	    // =======================================================
	    // check adjacent vertices of the v_g1 (OUT edges)
	    // =======================================================
	    typename boost::graph_traits<G>::out_edge_iterator o_i, o_end;
	    for (boost::tie(o_i,o_end) = out_edges(v_g1, g1); o_i != o_end; ++o_i)
	    {
		EDescr e_g1 = *o_i;
		EIndex ei_g1 = dm1.get_edge_index(e_g1);
		VDescr v_g1_adj = target(e_g1, g1);
		VIndex vi_g1_adj = dm1.get_vertex_index(v_g1_adj);
		if (t1->v_core[vi_g1_adj] != NULL_VINDEX)
		{
		    VIndex vi_g2_adj = t1->v_core[vi_g1_adj];
		    VDescr v_g2_adj = dm2.get_vertex_descriptor(vi_g2_adj);
		    
		    // if exist the edge (v_g2 -> v_g2_adj)
		    EDescr e_g2;
		    if (find_edge(v_g2, v_g2_adj, g2, e_g2) && ec(g1, g2, e_g1, e_g2))
		    {
			if (added_edges)
			{
			    EIndex ei_g2 = dm2.get_edge_index(e_g2);
			    added_edges->push_back(EIndexPair(ei_g2,ei_g1));
			}
		    }
		    else
			if (exit_if_no_edge)
			    return false;
		}
		else
		{
		    if (t1->t[vi_g1_adj]) ++*termout;
		    if (!t1->t[vi_g1_adj]) ++*nnew;
		}
	    }

	    return true;
	}


	template<class G, class D>
	void UnDirectedPolicy<G,D>::TArray::make_tarray(VIndex vi_g1, TCount*cnt, int depth)
	{
	    const G& g = this->graph;
	    const DM& dm = this->dm;

	    if (t[vi_g1] == 0) t[vi_g1] = depth; else --cnt->t_len;
	    
	    VDescr v = dm.get_vertex_descriptor(vi_g1);

	    typename boost::graph_traits<G>::out_edge_iterator o_i, o_end;
	    for (boost::tie(o_i,o_end) = out_edges(v, g); o_i != o_end; ++o_i)
	    {
		VIndex vi_adj = dm.get_vertex_index(target(*o_i, g));
		if (t[vi_adj] == 0)
		{
		    t[vi_adj] = depth;
		    ++cnt->t_len;
		}
	    }
	}


	template<class G, class D>
	void UnDirectedPolicy<G,D>::TArray::backtrack_tarray(VIndex vi_last, int depth)
	{
	    if (t[vi_last] == depth) t[vi_last] = 0;

	    VDescr v = this->dm.get_vertex_descriptor(vi_last);
	    typename boost::graph_traits<G>::out_edge_iterator o_i, o_end;
	    for (boost::tie(o_i,o_end) = out_edges(v, this->graph); o_i != o_end; ++o_i)
	    {
		VIndex vi_adj = this->dm.get_vertex_index(target(*o_i, this->graph));
		if (t[vi_adj] == depth) t[vi_adj] = 0;
	    }
	}


	// type selection
        template<class G, class D, class DirTag>
        struct DirPolicy_ : public DirectedPolicy<G,D> {};

        template<class G, class D>
        struct DirPolicy_<G,D,boost::undirected_tag> : public UnDirectedPolicy<G,D> {};

        template<class G, class D>
        struct DirPolicy
            : public DirPolicy_<G,D,typename boost::graph_traits<G>::directed_category> {};



	///////////////////////////////////////////////////////////////////////
        //              class State
        // --------------------------------------------------------------------
	template<class DP, class MP, class VC, class EC>
	class State
	{
	    typedef typename DP::Graph Graph;
	    typedef typename DP::DM DM;
	    typedef typename DP::TCount TCount;
	    typedef typename DP::TArray TArray;
            typedef typename boost::graph_traits<Graph>::vertex_descriptor VDescr;
            typedef typename boost::graph_traits<Graph>::edge_descriptor EDescr;

	    unsigned int depth;
	    struct MPart
	    {
		TArray* tarr;
		TCount  tcnt;
		VIndex vi_last;
		MPart(TArray* t, const TCount& cnt = TCount(), VIndex vi = NULL_VINDEX)
		    :tarr(t), tcnt(cnt), vi_last(vi) {}
	    } mp1, mp2;

	    EIndexPairs last_mapped_edges;

	    const VC& vc;
	    const EC& ec;
	    
	    bool test_feasibility_and_add(VIndex vi_g1, VIndex vi_g2);
	    void backtrack();
	public:
	    class NotFeasibleException {};

	    State(TArray* tarr1, TArray* tarr2, const VC& vc, const EC& ec)
		:depth(0),
		 mp1(tarr1),
		 mp2(tarr2),
		 vc(vc), ec(ec)
		{
		    //print();
		}
	    
	    State(const State& s, VIndex vi_g1, VIndex vi_g2)
		:depth(s.depth+1),
		 mp1(s.mp1.tarr, s.mp1.tcnt, vi_g1),
		 mp2(s.mp2.tarr, s.mp2.tcnt, vi_g2),
		 vc(s.vc), ec(s.ec)
		{
		    if (! test_feasibility_and_add(vi_g1, vi_g2))
			throw NotFeasibleException();
		    //print();
		}

	    ~State() { backtrack(); }
	    
	    bool is_goal() const;
	    bool is_dead() const { return TCount::template cmp(mp1.tcnt, mp2.tcnt, &MP::op); }
	    IndexIteratorPair get_pairs() const
		{ return TArray::get_pairs(mp1.tarr, mp1.tcnt, mp2.tarr, mp2.tcnt); }
	    
	    const IsoMap<Graph, DM>& iso_map1() const { return *mp1.tarr; }
	    const IsoMap<Graph, DM>& iso_map2() const { return *mp2.tarr; }
	    void print() const;
	};


	template<class DP, class MP, class VC, class EC>
	bool State<DP,MP,VC,EC>::test_feasibility_and_add(VIndex vi_g1, VIndex vi_g2)
	{
	    const Graph& g1 = mp1.tarr->graph;
	    const Graph& g2 = mp1.tarr->graph;
	    const DM& dm1 = mp1.tarr->dm;
	    const DM& dm2 = mp2.tarr->dm;

	    VDescr v_g1 = dm1.get_vertex_descriptor(vi_g1);
	    VDescr v_g2 = dm2.get_vertex_descriptor(vi_g2);
	    
            // =======================================================
            // test feasibility
            // =======================================================
	    
	    if (! vc(g1, g2, v_g1, v_g2))
		return false;
	    
	    int termout1=0, termout2=0, termin1=0, termin2=0, new1=0, new2=0;
	    
	    if (! TArray::feasible(v_g1, v_g2, mp1.tarr, mp2.tarr,
				   &termout1, &termin1, &new1,
				   0, ec, MP::chk_exit))
		return false;


	    if (! TArray::feasible(v_g2, v_g1, mp2.tarr, mp1.tarr,
				   &termout2, &termin2, &new2,
				   &last_mapped_edges, ec, true))
		return false;

	    if (! MP::check_term_count(termout1, termout2, termin1, termin2, new1, new2))
		return false;

            // =======================================================
            // add
            // =======================================================
	    
	    mp1.tarr->v_core[vi_g1] = vi_g2;
	    mp2.tarr->v_core[vi_g2] = vi_g1;
	    std::for_each(last_mapped_edges.begin(), last_mapped_edges.end(), MM1(mp1.tarr->e_core));
	    std::for_each(last_mapped_edges.begin(), last_mapped_edges.end(), MM2(mp2.tarr->e_core));

	    mp1.tarr->make_tarray(vi_g1, &mp1.tcnt, depth);
	    mp2.tarr->make_tarray(vi_g2, &mp2.tcnt, depth);

	    mp1.vi_last = vi_g1;
	    mp2.vi_last = vi_g2;
	    
	    return true;
	}


	template<class DP, class MP, class VC, class EC>
	void State<DP,MP,VC,EC>::backtrack()
	{
	    if (mp1.vi_last == NULL_VINDEX)
	    {
		assert (mp2.vi_last == NULL_VINDEX);
		return;
	    }

	    assert (mp1.vi_last != NULL_VINDEX);
	    assert (mp2.vi_last != NULL_VINDEX);

	    mp1.tarr->v_core[mp1.vi_last] = NULL_VINDEX;
	    mp2.tarr->v_core[mp2.vi_last] = NULL_VINDEX;
	    std::for_each(last_mapped_edges.begin(), last_mapped_edges.end(), M1(mp1.tarr->e_core));
	    std::for_each(last_mapped_edges.begin(), last_mapped_edges.end(), M2(mp2.tarr->e_core));
	    
	    mp1.tarr->backtrack_tarray(mp1.vi_last, depth);
	    mp2.tarr->backtrack_tarray(mp2.vi_last, depth);
	}



	template<class DP, class MP, class VC, class EC>
	void State<DP,MP,VC,EC>::print() const
	{
            ::fprintf(std::cerr, "*********************************************************\n");
            ::fprintf(std::cerr, "depth = %d\n", depth);
	    print(std::cerr, *mp1.tarr, *mp2.tarr, 1);
	    print(std::cerr, *mp2.tarr, *mp1.tarr, 2);
	}

	
	bool exists_unmapped_edges(const std::vector<EIndex> e_core)
	{
	    typedef std::vector<EIndex>::const_iterator Eci;
	    return std::find(e_core.begin(), e_core.end(), NULL_EINDEX) != e_core.end();
	}


	template<class DP, class MP, class VC, class EC>
	bool State<DP,MP,VC,EC>::is_goal() const
	{ 
	    if (! mp2.tarr->e_core.empty())
		return ! exists_unmapped_edges(mp2.tarr->e_core);
	    else
		return depth == num_vertices(mp2.tarr->graph);
	}

	///////////////////////////////////////////////////////////////////////
        //              match_all()
        // --------------------------------------------------------------------
        //

	template<class S, class R>
	void match_all(const S& s, R& result)
	{
	    if (s.is_goal())
	    {
		std::cerr << "IsGoal!\n";
		//s.print();
		result(s.iso_map1(), s.iso_map2());
		return;
	    }

	    if (s.is_dead())
	    {
		std::cerr << "IsDead!\n";
		return;
	    }

	    IndexIteratorPair ip = s.get_pairs();
            if (ip.second.get_v() == NULL_VINDEX)
	    {
		std::cerr << "exit_1\n";
                return;
	    }
            while (ip.first.get_v() != NULL_VINDEX)
            {
		try
		{
                    S h(s, ip.first.get_v(), ip.second.get_v());
                    match_all(h, result);
		}
		catch (typename S::NotFeasibleException) { /* just continue */ }
                ip.first.next();
            }

	    std::cerr << "exit_2\n";
	}


	///////////////////////////////////////////////////////////////////////
        //              Defaults
        // --------------------------------------------------------------------
        //
	template<class G>
	class DMDefault
	{
            typedef typename boost::graph_traits<G>::vertex_descriptor VDescr;
            typedef typename boost::graph_traits<G>::edge_descriptor EDescr;
	    std::vector<EDescr> i2e;
	public:
	    class BadDescriptorException {};
	    DMDefault(const G& g)
		{
		    i2e.reserve(num_edges(g));
		    typename boost::graph_traits<G>::edge_iterator i, i_end;
		    for (boost::tie(i,i_end) = edges(g); i != i_end; ++i)
			i2e.push_back(*i);
		}
	    
	    VDescr get_vertex_descriptor(VIndex i) const { return i;}
	    VIndex get_vertex_index(VDescr v) const { return v; }
	    EDescr get_edge_descriptor(EIndex i) const { return i2e.at(i); }
	    EIndex get_edge_index(EDescr e) const
		{
		    EIndex n = i2e.size();
                    for (EIndex i = 0; i < n; ++i) if (i2e[i] == e) return i;
                    throw BadDescriptorException();
                    return NULL_EINDEX;
		}	    
	};

        template<class G>
        struct VertexDefaultCompatible {
            typedef typename boost::graph_traits<G>::vertex_descriptor VDescr;
            bool operator() (const G&, const G&, VDescr, VDescr) const { return true; }
        };

        template<class G>
        struct EdgeDefaultCompatible {
            typedef typename boost::graph_traits<G>::edge_descriptor EDescr;
            bool operator() (const G&, const G&, EDescr, EDescr) const { return true; }
        };	

	
	struct CountIsoResult
	{
	    int iso_count;
	    CountIsoResult() :iso_count(0) {}
	    template<class IM>
	    bool operator() (const IM&, const IM&) { ++iso_count; return true; }
	};


	struct PrintIsoResult
	{
	    template<class IM>
	    bool operator() (const IM& m1, const IM& m2)
		{
		    std::cout << "--------------------------------------------------------------\n";
		    print(std::cout, m1, m2, 1);
		    print(std::cout, m2, m1, 2);
		    return true;
		}
	};

    } // end: namespace detail


    ///////////////////////////////////////////////////////////////////////
    //          graph_isomorphism_all()
    // --------------------------------------------------------------------
    //
    template<class G, class D, class VC, class EC, class Result>
    void graph_isomorphism_all(const G& g1, const G& g2,
                               const D& dm1, const D& dm2,
                               const VC& vc,
                               const EC& ec,
			       Result& result)
    {
        typedef detail::GGIsomorphismPolicy<G> IsoPolicy;
	typedef detail::DirPolicy<G,D> DirPolicy;
	
	typename DirPolicy::TArray tarr1(g1, dm1);
	typename DirPolicy::TArray tarr2(g2, dm2);
	detail::State<DirPolicy,IsoPolicy,VC,EC> state(&tarr1, &tarr2, vc, ec);
	match_all(state, result);
    }

    ///////////////////////////////////////////////////////////////////////
    //          subgraph_isomorphism_all()
    // --------------------------------------------------------------------
    //
    template<class G, class D, class VC, class EC, class Result>
    void subgraph_isomorphism_all(const G& g1, const G& g2,
				  const D& dm1, const D& dm2,
				  const VC& vc,
				  const EC& ec,
				  Result& result)
    {
        typedef detail::GSGIsomorphismPolicy<G> IsoPolicy;
	typedef detail::DirPolicy<G,D> DirPolicy;
	
	typename DirPolicy::TArray tarr1(g1, dm1);
	typename DirPolicy::TArray tarr2(g2, dm2);
	detail::State<DirPolicy,IsoPolicy,VC,EC> state(&tarr1, &tarr2, vc, ec);
	match_all(state, result);
    }



    template<class G>
    int graph_isomorphism_count(const G& g1, const G& g2)
    {
	detail::CountIsoResult result;
        graph_isomorphism_all(g1, g2,
                              detail::DMDefault<G>(g1), detail::DMDefault<G>(g2),
                              detail::VertexDefaultCompatible<G>(),
                              detail::EdgeDefaultCompatible<G>(),
			      result);
	return result.iso_count;
    }

    template<class G>
    void graph_isomorphism_all(const G& g1, const G& g2)
    {
	detail::PrintIsoResult result;
        graph_isomorphism_all(g1, g2,
                              detail::DMDefault<G>(g1), detail::DMDefault<G>(g2),
                              detail::VertexDefaultCompatible<G>(),
                              detail::EdgeDefaultCompatible<G>(),
			      result);
    }


    template<class G>
    void subgraph_isomorphism_all(const G& g1, const G& g2)
    {
	detail::PrintIsoResult result;
        subgraph_isomorphism_all(g1, g2,
				 detail::DMDefault<G>(g1), detail::DMDefault<G>(g2),
				 detail::VertexDefaultCompatible<G>(),
				 detail::EdgeDefaultCompatible<G>(),
				 result);
    }
    
}     // end: namespace graph_alg

#endif
