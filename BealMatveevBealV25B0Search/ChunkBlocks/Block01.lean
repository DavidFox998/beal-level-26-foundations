import BealMatveevBealV25B0Search.ChunkGroups.Group010
import BealMatveevBealV25B0Search.ChunkGroups.Group011
import BealMatveevBealV25B0Search.ChunkGroups.Group012
import BealMatveevBealV25B0Search.ChunkGroups.Group013
import BealMatveevBealV25B0Search.ChunkGroups.Group014
import BealMatveevBealV25B0Search.ChunkGroups.Group015
import BealMatveevBealV25B0Search.ChunkGroups.Group016
import BealMatveevBealV25B0Search.ChunkGroups.Group017
import BealMatveevBealV25B0Search.ChunkGroups.Group018
import BealMatveevBealV25B0Search.ChunkGroups.Group019

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_01 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 1 + 10 * g + i))
      (500 * (100 * 1 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_010 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_011 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_012 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_013 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_014 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_015 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_016 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_017 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_018 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_019 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
