import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1010
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1011
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1012
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1013
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1014
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1015
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1016
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1017
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1018
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1019

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_101 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 101 + i)) (500 * (10 * 101 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1010
  by_cases h1 : i = 1
  · subst i
    exact chunk_1011
  by_cases h2 : i = 2
  · subst i
    exact chunk_1012
  by_cases h3 : i = 3
  · subst i
    exact chunk_1013
  by_cases h4 : i = 4
  · subst i
    exact chunk_1014
  by_cases h5 : i = 5
  · subst i
    exact chunk_1015
  by_cases h6 : i = 6
  · subst i
    exact chunk_1016
  by_cases h7 : i = 7
  · subst i
    exact chunk_1017
  by_cases h8 : i = 8
  · subst i
    exact chunk_1018
  by_cases h9 : i = 9
  · subst i
    exact chunk_1019
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
