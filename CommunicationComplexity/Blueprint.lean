import Architect
import CommunicationComplexity.Basic
import CommunicationComplexity.Rectangle.Basic
import CommunicationComplexity.Deterministic.Basic
import CommunicationComplexity.Deterministic.FiniteMessage
import CommunicationComplexity.Deterministic.UpperBounds
import CommunicationComplexity.Deterministic.Subprotocol
import CommunicationComplexity.Deterministic.Rectangle
import CommunicationComplexity.Deterministic.BalancedSimulation
import CommunicationComplexity.Deterministic.Rank
import CommunicationComplexity.PrivateCoin.Basic
import CommunicationComplexity.PrivateCoin.FiniteMessage
import CommunicationComplexity.Trees.Basic
import CommunicationComplexity.Examples.Equality

namespace CommunicationComplexity

namespace Rectangle

attribute [blueprint] IsRectangle IsRectangle_iff IsMonochromatic IsMonoPartition

namespace IsMonoPartition

attribute [blueprint] exists_mem eq_of_mem cross_mem apply_eq

end IsMonoPartition
end Rectangle

namespace Deterministic

attribute [blueprint] communicationComplexity
  communicationComplexity_le_iff
  communicationComplexity_le_iff_finiteMessage
  le_communicationComplexity_iff
  communicationComplexity_le_clog_card
  communicationComplexity_le_clog_card_X_alpha
  communicationComplexity_le_clog_card_Y_alpha
  mono_partition_of_communicationComplexity_le
  communicationComplexity_lower_bound

namespace Protocol

attribute [blueprint] Protocol run complexity equiv computes swap
  swap_run swap_complexity alice_to_bob bob_to_alice
  shape numLeaves
  IsSubprotocol IsSubprotocol.trans
  balanced_subprotocol
  SubprotocolPath SubprotocolPath.toIsSubprotocol
  path_exists_of_isSubprotocol SubprotocolPath.numLeaves_le
  reachXPath reachYPath reachesPath reachX reachY reaches
  subprotocol_run_eq_of_reachesPath subprotocol_run_eq_of_reaches
  chooseOutput erasePath erasePath_numLeaves erasePath_run_outside
  erase_numLeaves erase_run_outside
  deletePath deletePath_ne_none_of_lt deletePath_exists_of_lt
  prunePath_spec eq_of_deletePath_none deletePath_numLeaves_of_some
  prunePath_numLeaves_of_lt reachesPath_of_deletePath_none
  deletePath_run_outside_of_some
  prunePath_run_outside_of_lt prune_numLeaves_of_lt prune_run_outside_of_lt
  testSubprotocol_run_inside testSubprotocol_run_outside
  leafRectangles leafRectangles_isRectangle
  leafRectangles_cover leafRectangles_disjoint leafRectangles_mono
  leafRectangles_card leafRectangles_isMonoPartition rectangle_partition
  reachesPath_isRectangle reaches_isRectangle
  theorem_1_7_experiment

end Protocol

namespace FiniteMessage

attribute [blueprint] Protocol

namespace Protocol

attribute [blueprint] run complexity toProtocol ofProtocol
  ofProtocol_run ofProtocol_complexity ofProtocol_equiv

end Protocol
end FiniteMessage

namespace Rank

attribute [blueprint] boolFunctionMatrix boolFunctionRank rectMatrix
  rank_rectMatrix_le_one boolFunctionRank_le_ncard
  boolFunctionRank_le_pow_of_communicationComplexity_le
  log_rank_lower_bound

end Rank
end Deterministic

attribute [blueprint] Matrix.rank_add_le Matrix.rank_sum_le

namespace PrivateCoin

attribute [blueprint] communicationComplexity
  communicationComplexity_le_iff
  communicationComplexity_le_of_protocol
  le_communicationComplexity_iff
  communicationComplexity_le_iff_finiteMessage
  communicationComplexity_le_of_finiteMessage_protocol
  communicationComplexity_le_deterministic

namespace Protocol

attribute [blueprint] Protocol run complexity swap swap_run
  swap_complexity measurable_preimage_run approx_computes

end Protocol

namespace FiniteMessage

attribute [blueprint] Protocol

namespace Protocol

attribute [blueprint] run complexity ofProtocol ofProtocol_run
  ofProtocol_complexity toProtocol ofProtocol_equiv

end Protocol
end FiniteMessage
end PrivateCoin

namespace TreeLemma

attribute [blueprint] balanced_subtree

end TreeLemma

namespace Examples.Equality

attribute [blueprint] eq communicationComplexity_le communicationComplexity_zero
  le_communicationComplexity communicationComplexity_eq

end Examples.Equality

end CommunicationComplexity
