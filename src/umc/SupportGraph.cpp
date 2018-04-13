#include "SupportGraph.h"

#include <iostream>
#include <fstream>
#include <sstream>

namespace UMC {

  std::map<int, std::set<CubeID> > SupportGraphDotWriter::computeRanks() const {
    std::map<int, std::set<CubeID> > ranks;
    auto cube_range = graph.getKnownCubeIDs();
    for(auto it = cube_range.first; it != cube_range.second; ++it) {
      CubeID id = *it;
      if(id != property_id) {
        int level = graph.getLevel(id);
        // Leave nodes for which we don't have a level free
        if(level >= 0) {
          ranks[level].insert(id);
        }
      }
    }

    return ranks;
  }

  std::unordered_map<CubeID, unsigned > SupportGraphDotWriter::computeOutDegrees() const {
    std::unordered_map<CubeID, unsigned > cube_to_outdegree;
    auto known_cube_range = graph.getKnownCubeIDs();
    for(auto it = known_cube_range.first; it != known_cube_range.second; ++it) {
      CubeID cube = *it;
      cube_to_outdegree[cube] = 0;
    }

    auto supp_cube_range = graph.getSupportedCubeIDs();
    for(auto it = supp_cube_range.first; it != supp_cube_range.second; ++it) {
      CubeID supported = *it;
      auto support_range = graph.getInEdges(supported);

      for(auto cube_it = support_range.first; cube_it != support_range.second; ++cube_it) {
        CubeID cube = *cube_it;
        cube_to_outdegree[cube]++;
      }
    }
    return cube_to_outdegree;
  }

  std::unordered_map<CubeID, unsigned>& SupportGraphDotWriter::getOutDegrees() {
    return cube_to_outdegree;
  }

  std::set<CubeID> SupportGraphDotWriter::findTransitiveSupport(CubeID cube) const {
    std::set<CubeID> support;
    support.insert(cube);
    findTransitiveSupport(support);
    return support;
  }

  // Not as efficient as it could be
  void SupportGraphDotWriter::findTransitiveSupport(std::set<CubeID> & support) const {
    std::set<CubeID> support_updated = support;
    for(auto it = support.begin(); it != support.end(); ++it) {
      CubeID cube = *it;
      auto support_range = graph.getInEdges(cube);
      support_updated.insert(support_range.first, support_range.second);
    }

    if(support_updated.size() > support.size()) {
      support = support_updated;
      findTransitiveSupport(support);
    }
  }

  std::string SupportGraphDotWriter::dotPreamble() const {
    return "digraph support_graph {";
  }

  std::string SupportGraphDotWriter::dotPostamble() const {
    return "}";
  }

  std::string SupportGraphDotWriter::dotCubeIdentifier(CubeID cube) const {
    return "c_" + std::to_string(cube);
  }

  std::string SupportGraphDotWriter::dotParams(const ParamMap & params) const {
    if(params.empty()) {
      return "";
    }

    std::stringstream ss;

    ss << "[";
    for(auto pv : params) {
      std::string param = pv.first;
      std::string value = pv.second;

      // Dot tools seem to accept the extra commas, so we'll leave them
      // (e.g., [color=red,])
      ss << param << "=" << value << ",";
    }
    ss << "]";

    return ss.str();
  }

  std::string SupportGraphDotWriter::dotCube(CubeID cube) const {
    std::stringstream ss;
    bool necessary = proof_cubes.find(cube) != proof_cubes.end();

    std::string label = std::to_string(cube);

    unsigned in_degree = graph.getInDegree(cube);
    unsigned out_degree = cube_to_outdegree.at(cube);
    int level = graph.getLevel(cube);
    bool bad = graph.isBad(cube);

    std::string annotation = "";
    if(graph.hasAnnotation(cube)) {
      annotation = "[" + graph.getAnnotation(cube) + "]";
    }

    std::stringstream tooltip_ss;
    tooltip_ss << "\""
               << "F_" << (level == INT_MAX ? "inf" : std::to_string(level)) << " "
               << "in = " << in_degree << " "
               << "out = " << out_degree << " "
               << annotation
               << "\"";
    std::string tooltip = tooltip_ss.str();


    std::string color = "black";
    if(level == INT_MAX) {
      color = "orange";
    } else if(level == 0) {
      color = "grey";
    }
    if(necessary) {
      color = "red";
    }
    if(cube == property_id) {
      color = "\"#008B45\""; // Dark green
    }

    if(bad) {
      assert(level < INT_MAX);
      assert(cube != property_id);
      color = "dodgerblue";
    }

    ParamMap p = {{ "label", "\"" + label + "\""},
                  { "fontcolor", color },
                  { "color", color },
                  { "tooltip", tooltip }};

    ss << dotCubeIdentifier(cube)
       << dotParams(p)
       << ";";

    return ss.str();
  }

  std::string SupportGraphDotWriter::dotEdge(CubeID from, CubeID to) const {
    std::stringstream ss;

    bool from_necessary = proof_cubes.find(from) != proof_cubes.end();
    bool to_necessary = proof_cubes.find(to) != proof_cubes.end();
    std::string edgecolor = "black";
    if(to_necessary) {
      edgecolor = "red";
    } else if(from_necessary) {
      edgecolor = "orange";
    }

    ParamMap p = {{"color", edgecolor}};

    ss << dotCubeIdentifier(from)
       << " -> "
       << dotCubeIdentifier(to)
       << dotParams(p)
       << ";";

    return ss.str();
  }

  void SupportGraphDotWriter::writeInfDot(std::ostream & os) const {
    os << dotPreamble() << std::endl;

    auto cube_range = graph.getKnownCubeIDs();

    // Declare nodes
    for(auto it = cube_range.first; it != cube_range.second; ++it) {
      CubeID id = *it;
      if(graph.getLevel(id) == INT_MAX || id == property_id) {
        os << dotCube(id) << std::endl;
      }
    }

    // Output edges
    for(auto it = cube_range.first; it != cube_range.second; ++it) {
      CubeID id = *it;

      if(graph.getLevel(id) != INT_MAX && id != property_id) { continue; }
      auto support_range = graph.getInEdges(id);
      for(auto support_it = support_range.first; support_it != support_range.second; ++support_it) {
        CubeID support_id = *support_it;
        if(graph.getLevel(support_id) == INT_MAX || id == property_id) {
          os << dotEdge(support_id, id) << std::endl;;
        }
      }
    }

    os << dotPostamble() << std::endl;
  }

  void SupportGraphDotWriter::writeDot(std::ostream & os) const {
    os << dotPreamble() << std::endl;

    auto known_cube_range = graph.getKnownCubeIDs();
    auto supported_cube_range = graph.getSupportedCubeIDs();

    // Output edges
    // Suppress vertices for cubes in F_inf that have no out edges
    std::set<CubeID> suppressed_cubes;
    if(ranked_cubes.find(INT_MAX) != ranked_cubes.end()) {
     suppressed_cubes = ranked_cubes.at(INT_MAX);
    }
    suppressed_cubes.insert(property_id);

    std::stringstream edge_ss;
    for(auto it = supported_cube_range.first; it != supported_cube_range.second; ++it) {
      CubeID id = *it;

      if(id == property_id) {
        continue;
      }

      auto support_range = graph.getInEdges(id);
      bool id_inf = graph.getLevel(id) == INT_MAX;


      for(auto support_it = support_range.first; support_it != support_range.second; ++support_it) {
        CubeID support_id = *support_it;

        bool support_inf = graph.getLevel(support_id) == INT_MAX;

        // Don't put edges between infinity lemmas in, and also don't
        // draw edges involving the property
        if(id != property_id && (!id_inf || !support_inf)) {
          edge_ss << dotEdge(support_id, id) << std::endl;
          suppressed_cubes.erase(id);
          suppressed_cubes.erase(support_id);
        }
      }
    }

    // Declare nodes that we want to show
    for(auto it = known_cube_range.first; it != known_cube_range.second; ++it) {
      CubeID id = *it;
      if(suppressed_cubes.find(id) == suppressed_cubes.end()) {
        os << dotCube(id) << std::endl;
      }
    }

    // Arrange nodes into ranks by level. ranked_cubes should be an ordered
    // map for this to work
    // Lots of hacks in here
    for(auto it = ranked_cubes.begin(); it != ranked_cubes.end(); ++it) {
      int level = it->first;

      if(level == INT_MAX) {
        os << "[style=invis]";
      }

      os << std::endl;
      if(level == 0 || level == INT_MAX) {
        os << "{rank=source; ";
      } else {
        os << "{rank=same; ";
      }

      const std::set<CubeID> & cubes_at_rank = it->second;
      for(auto cube_it = cubes_at_rank.begin(); cube_it != cubes_at_rank.end(); ++cube_it) {
        CubeID id = *cube_it;
        assert(id != property_id);
        if(suppressed_cubes.find(id) == suppressed_cubes.end()) {
          os << dotCubeIdentifier(id) << " ";
        }
      }
      os << "}";
    }

    // Add one invisible edge between each pair of consecutive ranks,
    // just in case there are not real ones

    ID last_id = CUBE_ID_NULL;
    for(auto it = ranked_cubes.begin(); it != ranked_cubes.end(); ++it) {
      const std::set<CubeID> & cubes_at_rank = it->second;
      if(!cubes_at_rank.empty()) {
        CubeID id = (*cubes_at_rank.begin());
        if(last_id != CUBE_ID_NULL) {
          os << dotCubeIdentifier(last_id) << " -> " << dotCubeIdentifier(id) << "[style=invis];" << std::endl;
        }
        last_id = id;
      }
    }

    os << edge_ss.str() << std::endl;

    os << dotPostamble() << std::endl;
  }

  /***
  Add an edge to the graph. It must not already exist.
  ***/
  void SupportGraph::addEdge(CubeID from, CubeID to) {
    assert(inductive_trace.isKnown(from));
    assert(inductive_trace.isKnown(to));

    assert(cube_in_edges[to].find(from) == cube_in_edges[to].end());
    assert(cube_out_edges[from].find(to) == cube_out_edges[from].end());

    cube_in_edges[to].insert(from);
    cube_out_edges[from].insert(to);

    known_cubes.insert(to);
    known_cubes.insert(from);
    supported_cubes.insert(to);
  }

  /***
  Remove an edge from the graph. The edge must exist.
  ***/
  void SupportGraph::removeEdge(CubeID from, CubeID to) {
    assert(removeEdgeIfExists(from, to));
  }

  /***
  Remove an edge from the graph, returning true if and only if the
  edge was present to begin with
  ***/
  bool SupportGraph::removeEdgeIfExists(CubeID from, CubeID to) {
    SupportSet & in_edges = cube_in_edges[to];
    SupportSet & out_edges = cube_out_edges[from];

    auto in_iter = in_edges.find(from);
    auto out_iter = out_edges.find(to);

    bool in_present = in_iter != in_edges.end();
    bool out_present = out_iter != out_edges.end();

    // If the edge is only represented in one direction that's bad
    assert(in_present == out_present);

    bool present = in_present;
    if(present) {
      in_edges.erase(in_iter);
      out_edges.erase(out_iter);
      return true;
    } else {
      return false;
    }
  }

  unsigned SupportGraph::countLits(const SupportSet & ss) const {
    unsigned total = 0;
    for(CubeID id : ss) {
      assert(inductive_trace.isKnown(id));
      total += inductive_trace.getCube(id).size();
    }

    return total;
  }

  bool SupportGraph::isBetter(const SupportSet & lhs, const SupportSet & rhs) const {
    if(lhs == rhs) {
      return false;
    }

    if(lhs.size() < rhs.size()) {
      return true;
    } else if (rhs.size() < lhs.size()) {
      return false;
    }

    // Size is equal

    size_t lhs_lits = countLits(lhs);
    size_t rhs_lits = countLits(rhs);

    if(lhs_lits < rhs_lits) {
      return true;
    } else if(rhs_lits < lhs_lits) {
      return false;
    }

    // Size and total literals is equal
    // Break tie arbitrarily based on Cube IDs
    auto lhs_it = lhs.begin();
    auto rhs_it = rhs.begin();

    while(lhs_it != lhs.end() && rhs_it != rhs.end()) {
      CubeID lhs_id = *lhs_it;
      CubeID rhs_id = *rhs_it;

      if(lhs_id < rhs_id) {
        return true;
      } else if(rhs_id < lhs_id) {
        return false;
      }

      lhs_it++;
      rhs_it++;
    }

    // We can only get here if they are the same, but we already
    // checked that at the beginning
    assert(false);
  }

  std::string SupportGraph::getAnnotation(const Cube & cube) const {
    (void) cube;
    return "";
  }

  std::string SupportGraph::getAnnotation(CubeID cube) const {
    (void) cube;
    return "";
  }

  bool SupportGraph::hasAnnotation(const Cube & cube) const {
    (void) cube;
    return false;
  }

  bool SupportGraph::hasAnnotation(CubeID cube) const {
    (void) cube;
    return false;
  }

  void SupportGraph::deleteCube(const Cube & cube) {
    CubeID id = inductive_trace.getID(cube);
    deleteCube(id);
  }

  void SupportGraph::deleteCube(const CubeID id) {
    auto known_range = getKnownCubeIDs();
    for(auto it = known_range.first; it != known_range.second; ++it) {
      CubeID known_id = *it;
      if(hasSupportSet(known_id)) {
        auto support_range = getInEdges(known_id);
        std::set<CubeID> support_set(support_range.first, support_range.second);
        if(support_set.find(id) != support_set.end()) {
          deleteSupport(known_id);
        }
      }
    }
  }

  void SupportGraph::recordSupport(const std::set<Cube> & support_set, const Cube & supported) {
    SupportSet ss;
    for(auto it = support_set.begin(); it != support_set.end(); ++it) {
      assert(inductive_trace.isKnown(*it));
      CubeID ss_id = inductive_trace.getID(*it);
      ss.insert(ss_id);
    }

    assert(inductive_trace.isKnown(supported));
    CubeID supp = inductive_trace.getID(supported);

    recordSupport(ss, supp);
  }

  void SupportGraph::recordSupport(const std::set<CubeID> & support_set, CubeID & supported) {
    auto support_it = cube_in_edges.find(supported);

    if(support_it == cube_in_edges.end()) {
      // Just take the support set if we don't have one yet
      for(CubeID from_id : support_set) {
        addEdge(from_id, supported);
      }
    } else if(isBetter(support_set, support_it->second)) {
      deleteSupport(supported);

      for(CubeID from_id : support_set) {
        addEdge(from_id, supported);
      }
    }
  }

  /***
  Delete the support set of the cube.
  ***/
  void SupportGraph::deleteSupport(const Cube & supported) {
    CubeID id = inductive_trace.getID(supported);
    deleteSupport(id);
  }

  void SupportGraph::deleteSupport(CubeID & supported) {
    auto support_it = cube_in_edges.find(supported);
    if(support_it == cube_in_edges.end()) {
      // We already don't have one
      return;
    } else {
      auto old_range = getInEdges(supported);
      SupportSet old_ss(old_range.first, old_range.second);
      for(CubeID from_id : old_ss) {
        removeEdge(from_id, supported);
      }
    }
    cube_in_edges.erase(support_it);
    assert(cube_in_edges.find(supported) == cube_in_edges.end());
  }

  std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
  SupportGraph::getInEdges(const Cube & cube) const {
    CubeID id = inductive_trace.getID(cube);
    return getInEdges(id);
  }

  std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
  SupportGraph::getInEdges(CubeID id) const {
    static SupportSet null_support;
    auto it = cube_in_edges.find(id);
    if(it != cube_in_edges.end()) {
      return std::make_pair(it->second.begin(), it->second.end());
    } else {
      return std::make_pair(null_support.end(), null_support.end());
    }
  }

  std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
  SupportGraph::getOutEdges(const Cube & cube) const {
    CubeID id = inductive_trace.getID(cube);
    return getOutEdges(id);
  }

  std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
  SupportGraph::getOutEdges(CubeID id) const {
    static SupportSet null_support;
    auto it = cube_out_edges.find(id);
    if(it != cube_out_edges.end()) {
      return std::make_pair(it->second.begin(), it->second.end());
    } else {
      return std::make_pair(null_support.end(), null_support.end());
    }
  }

  std::pair<std::set<CubeID>::const_iterator, std::set<CubeID>::const_iterator>
  SupportGraph::getSupportedCubeIDs() const {
    return std::make_pair(supported_cubes.begin(), supported_cubes.end());
  }

  std::pair<std::set<CubeID>::const_iterator, std::set<CubeID>::const_iterator>
  SupportGraph::getKnownCubeIDs() const {
    return std::make_pair(known_cubes.begin(), known_cubes.end());
  }

  bool SupportGraph::hasSupportSet(const Cube & cube) const {
    CubeID id = inductive_trace.getID(cube);
    return hasSupportSet(id);
  }

  bool SupportGraph::hasSupportSet(CubeID id) const {
    return cube_in_edges.find(id) != cube_in_edges.end();
  }

  std::set<Cube> SupportGraph::getSupportSet(const Cube & cube) const {
    assert(hasSupportSet(cube));
    CubeID id = inductive_trace.getID(cube);
    std::set<Cube> supports;
    auto it = cube_in_edges.find(id);
    for (SupportSet::iterator supp_it=it->second.begin(); supp_it!=it->second.end(); supp_it++){
      supports.insert(inductive_trace.getCube(*supp_it));
    }
    return supports;
  }

  size_t SupportGraph::getInDegree(const Cube & cube) const {
    CubeID id = inductive_trace.getID(cube);
    return getInDegree(id);
  }

  size_t SupportGraph::getInDegree(CubeID id) const {
    auto it = cube_in_edges.find(id);
    if(it != cube_in_edges.end()) {
      return it->second.size();
    } else {
      return 0;
    }
  }

  bool SupportGraph::isBad(const Cube & cube) const {
    assert(inductive_trace.isKnown(cube));
    CubeID id = inductive_trace.getID(cube);
    return isBad(id);
  }

  bool SupportGraph::isBad(CubeID id) const {
    assert(inductive_trace.isKnown(id));
    return inductive_trace.getActiveLemma(id).bad;
  }

  size_t SupportGraph::getOutDegree(const Cube & cube) const {
    CubeID id = inductive_trace.getID(cube);
    return getOutDegree(id);
  }

  size_t SupportGraph::getOutDegree(CubeID id) const {
    auto it = cube_out_edges.find(id);
    if(it != cube_out_edges.end()) {
      return it->second.size();
    } else {
      return 0;
    }
  }

  int SupportGraph::getLevel(const Cube & cube) const {
    assert(inductive_trace.isKnown(cube));
    CubeID id = inductive_trace.getID(cube);
    return getLevel(id);
  }

  int SupportGraph::getLevel(CubeID id) const {
    assert(inductive_trace.isKnown(id));
    const Lemma & lem = inductive_trace.getActiveLemma(id);
    return lem.level;
  }

  /***
  Get the minimum level of all cubes in the given cube's support set.
  Returns 0 if the cube has no support set.
  ***/
  int SupportGraph::getMinSupportLevel(const Cube & cube) const {
    CubeID id = inductive_trace.getID(cube);
    return getMinSupportLevel(id);
  }

  int SupportGraph::getMinSupportLevel(CubeID id) const {
    if (!hasSupportSet(id))
      return 0;

    auto it = cube_in_edges.find(id);
    int min_lv = INT_MAX;
    for (SupportSet::iterator supp_it=it->second.begin(); supp_it!=it->second.end(); supp_it++){
      min_lv = std::min(min_lv, getLevel(*supp_it));
    }
    return min_lv;
  }

  void SupportGraph::findUnsupportedCubes(const Cube & init_cube, std::set<CubeID> & unsupported_cubes) const {
    auto known_range = getKnownCubeIDs();

    // Not as efficient as possible but good enough
    bool found_new = true;
    while(found_new) {
      found_new = false;

      for(auto cube_it = known_range.first; cube_it != known_range.second; ++cube_it) {
        CubeID cube_id = *cube_it;

        if(unsupported_cubes.find(cube_id) != unsupported_cubes.end()) {
          continue;
        }

        if(getLevel(cube_id) == 0) {
          const Cube & cube = inductive_trace.getCube(cube_id);
          assert(cube.size() == 1);
          ID lit = cube[0];

          if(std::find(init_cube.begin(), init_cube.end(), lit) == init_cube.end()) {
            unsupported_cubes.insert(cube_id);
            found_new = true;
          }
        } else if(hasSupportSet(cube_id)) {
          auto support_range = getInEdges(cube_id);

          for(auto support_it = support_range.first; support_it != support_range.second; ++support_it) {
            CubeID supporting_cube_id = *support_it;

            if(unsupported_cubes.find(supporting_cube_id) != unsupported_cubes.end()) {
              unsupported_cubes.insert(cube_id);
              found_new = true;
            }
          }
        } else {
          // We don't know a support set for this cube
          unsupported_cubes.insert(cube_id);
          found_new = true;
        }
      }
    }
  }

  void SupportGraph::writeDot(const std::string & file, const Cube & property) const {
    std::ofstream dot_file;
    dot_file.open(file, std::ios::out);
    writeDot(dot_file, property);
    dot_file.close();
  }

  void SupportGraph::writeDot(std::ostream & os, const Cube & property) const {
    CubeID property_id = CUBE_ID_NULL;
    if(!property.empty()) {
      assert(inductive_trace.isKnown(property));
      property_id = inductive_trace.getID(property);
    }

    SupportGraphDotWriter writer(*this, property_id);
    writer.writeDot(os);
  }

  void SupportGraph::writeInfDot(const std::string & file, const Cube & property) const {
    std::ofstream dot_file;
    dot_file.open(file, std::ios::out);
    writeInfDot(dot_file, property);
    dot_file.close();
  }

  void SupportGraph::writeInfDot(std::ostream & os, const Cube & property) const {
    CubeID property_id = CUBE_ID_NULL;
    if(!property.empty()) {
      assert(inductive_trace.isKnown(property));
      property_id = inductive_trace.getID(property);
    }

    SupportGraphDotWriter writer(*this, property_id);
    writer.writeInfDot(os);
  }

  void SupportGraph::computeStats(const Cube & property, bool inf_only) {
    total=0;
    total_cnt=0;
    in_deg_dist.clear();
    out_deg_dist.clear();
    auto known_cube_range = getKnownCubeIDs();
    auto supp_cube_range = getSupportedCubeIDs();

    //count number of cubes in a level lower than infinity with no support set
    unknown_supp=0;
    for (auto it=known_cube_range.first; it!=known_cube_range.second; it++){
      if (getLevel(*it) >0 && !hasSupportSet(*it))
        unknown_supp++;
    }

    CubeID property_id = CUBE_ID_NULL;
    std::unordered_map<CubeID, unsigned> outdegrees;
    std::set<CubeID> transitive_support;
    if(!property.empty() && inductive_trace.isKnown(property)) {
      property_id = inductive_trace.getID(property);
      // TODO: this should not construct a dot writer
      SupportGraphDotWriter writer(*this, property_id);
      outdegrees = writer.getOutDegrees();
      transitive_support = writer.findTransitiveSupport(inductive_trace.getID(property));
    }


    //compute frequency distribution of indegrees
    for (auto it=supp_cube_range.first; it!=supp_cube_range.second; it++){
      if (inf_only && getLevel(*it) != INT_MAX) continue;
      if (getLevel(*it) == -1) continue;

      //count number of cubes and supports (in degree)
      int num_supports = cube_in_edges[*it].size();
      total += num_supports;
      total_cnt++;

      while ((int)in_deg_dist.size() <= num_supports)
        in_deg_dist.push_back(0);
      in_deg_dist[num_supports]++;
    }

    //compute frequency distribution of outdegrees
    for (auto it=outdegrees.begin(); it!=outdegrees.end(); it++){
      if (inf_only && getLevel(it->first) != INT_MAX) continue;
      if (getLevel(it->first) == -1) continue;
      while (out_deg_dist.size() <= it->second)
        out_deg_dist.push_back(0);
      out_deg_dist[it->second]++;
    }

    needed_inits = 0;
    for (auto it = transitive_support.begin(); it != transitive_support.end(); it++){
      const Lemma & lem = inductive_trace.getActiveLemma(*it);
      if (lem.getCube() != property && lem.level == 0) {
        needed_inits++;
      }
    }
  }

  void SupportGraph::printStats(bool inf_only) {
    std::cout <<"\n";
    std::cout << (inf_only ? "Inf " : "") << "Support Graph Statistics:" << std::endl;
    if (!inf_only) {
      std::cout << "Number of known cubes: " << known_cubes.size() << std::endl;
      std::cout << "Number of supported cubes: " << supported_cubes.size() << std::endl;
      std::cout << "Number of unsupported cubes (excluding initial): " << unknown_supp << std::endl;
    }
    std::cout << "Average support set size: " << (double)total/total_cnt << std::endl;
    std::cout << "Number of cubes: " << total_cnt << std::endl;
    std::cout << "Frequency distribution for in degree (cubes with support set only):";

    // TODO: compute median support in computeStats
    int median_support = -1;
    int total_cubes = 0;
    int total_nonzero = total_cnt;
    if (in_deg_dist.size() > 0) {
     total_nonzero -= in_deg_dist[0];
    }
    for (int i = 0; i < (int) in_deg_dist.size(); i++) {
      std::cout << " " << in_deg_dist[i];
      if (i > 0) {
        total_cubes += in_deg_dist[i];
        if (median_support < 0 && total_cubes >= total_nonzero / 2) {
          median_support = i;
        }
      }
    }
    std::cout << std::endl;

    std::cout << "Frequency distribution for out degree (all known cubes):";
    for (int i = 0; i < (int) out_deg_dist.size(); i++) {
        std::cout << " " << out_deg_dist[i];
    }
    std::cout << std::endl;
    std::cout << "Average number of support cubes: " << (double)total / total_nonzero << std::endl;
    std::cout << "Median number of support cubes: " << median_support << std::endl;
    if (!inf_only)
      std::cout << "Number of initial state literals needed to support the property: "
                << needed_inits << std::endl;
  }

}
