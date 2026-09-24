import BealMatveevBealV25B0Search.ChunkGroups.Group050
import BealMatveevBealV25B0Search.ChunkGroups.Group051
import BealMatveevBealV25B0Search.ChunkGroups.Group052
import BealMatveevBealV25B0Search.ChunkGroups.Group053
import BealMatveevBealV25B0Search.ChunkGroups.Group054
import BealMatveevBealV25B0Search.ChunkGroups.Group055
import BealMatveevBealV25B0Search.ChunkGroups.Group056
import BealMatveevBealV25B0Search.ChunkGroups.Group057
import BealMatveevBealV25B0Search.ChunkGroups.Group058
import BealMatveevBealV25B0Search.ChunkGroups.Group059

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_05 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 5 + 10 * g + i))
      (500 * (100 * 5 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_050 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_051 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_052 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_053 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_054 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_055 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_056 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_057 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_058 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_059 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
