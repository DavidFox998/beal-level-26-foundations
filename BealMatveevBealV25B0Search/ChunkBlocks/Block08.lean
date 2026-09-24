import BealMatveevBealV25B0Search.ChunkGroups.Group080
import BealMatveevBealV25B0Search.ChunkGroups.Group081
import BealMatveevBealV25B0Search.ChunkGroups.Group082
import BealMatveevBealV25B0Search.ChunkGroups.Group083
import BealMatveevBealV25B0Search.ChunkGroups.Group084
import BealMatveevBealV25B0Search.ChunkGroups.Group085
import BealMatveevBealV25B0Search.ChunkGroups.Group086
import BealMatveevBealV25B0Search.ChunkGroups.Group087
import BealMatveevBealV25B0Search.ChunkGroups.Group088
import BealMatveevBealV25B0Search.ChunkGroups.Group089

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_08 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 8 + 10 * g + i))
      (500 * (100 * 8 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_080 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_081 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_082 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_083 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_084 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_085 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_086 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_087 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_088 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_089 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
