import BealMatveevBealV25B0Search.ChunkGroups.Group040
import BealMatveevBealV25B0Search.ChunkGroups.Group041
import BealMatveevBealV25B0Search.ChunkGroups.Group042
import BealMatveevBealV25B0Search.ChunkGroups.Group043
import BealMatveevBealV25B0Search.ChunkGroups.Group044
import BealMatveevBealV25B0Search.ChunkGroups.Group045
import BealMatveevBealV25B0Search.ChunkGroups.Group046
import BealMatveevBealV25B0Search.ChunkGroups.Group047
import BealMatveevBealV25B0Search.ChunkGroups.Group048
import BealMatveevBealV25B0Search.ChunkGroups.Group049

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_04 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 4 + 10 * g + i))
      (500 * (100 * 4 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_040 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_041 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_042 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_043 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_044 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_045 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_046 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_047 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_048 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_049 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
