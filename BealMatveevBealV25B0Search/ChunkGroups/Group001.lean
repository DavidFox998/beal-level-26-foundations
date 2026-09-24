import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0010
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0011
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0012
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0013
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0014
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0015
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0016
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0017
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0018
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0019

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_001 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 1 + i)) (500 * (10 * 1 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0010
  by_cases h1 : i = 1
  · subst i
    exact chunk_0011
  by_cases h2 : i = 2
  · subst i
    exact chunk_0012
  by_cases h3 : i = 3
  · subst i
    exact chunk_0013
  by_cases h4 : i = 4
  · subst i
    exact chunk_0014
  by_cases h5 : i = 5
  · subst i
    exact chunk_0015
  by_cases h6 : i = 6
  · subst i
    exact chunk_0016
  by_cases h7 : i = 7
  · subst i
    exact chunk_0017
  by_cases h8 : i = 8
  · subst i
    exact chunk_0018
  by_cases h9 : i = 9
  · subst i
    exact chunk_0019
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
