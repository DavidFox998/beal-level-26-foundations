import BealMatveevBealV25B0Search.ChunkGroups.Group060
import BealMatveevBealV25B0Search.ChunkGroups.Group061
import BealMatveevBealV25B0Search.ChunkGroups.Group062
import BealMatveevBealV25B0Search.ChunkGroups.Group063
import BealMatveevBealV25B0Search.ChunkGroups.Group064
import BealMatveevBealV25B0Search.ChunkGroups.Group065
import BealMatveevBealV25B0Search.ChunkGroups.Group066
import BealMatveevBealV25B0Search.ChunkGroups.Group067
import BealMatveevBealV25B0Search.ChunkGroups.Group068
import BealMatveevBealV25B0Search.ChunkGroups.Group069

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_06 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 6 + 10 * g + i))
      (500 * (100 * 6 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_060 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_061 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_062 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_063 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_064 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_065 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_066 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_067 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_068 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_069 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
