import BealMatveevBealV25B0Search.ChunkGroups.Group000
import BealMatveevBealV25B0Search.ChunkGroups.Group001
import BealMatveevBealV25B0Search.ChunkGroups.Group002
import BealMatveevBealV25B0Search.ChunkGroups.Group003
import BealMatveevBealV25B0Search.ChunkGroups.Group004
import BealMatveevBealV25B0Search.ChunkGroups.Group005
import BealMatveevBealV25B0Search.ChunkGroups.Group006
import BealMatveevBealV25B0Search.ChunkGroups.Group007
import BealMatveevBealV25B0Search.ChunkGroups.Group008
import BealMatveevBealV25B0Search.ChunkGroups.Group009

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_00 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 0 + 10 * g + i))
      (500 * (100 * 0 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_000 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_001 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_002 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_003 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_004 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_005 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_006 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_007 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_008 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_009 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
