import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0920
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0921
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0922
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0923
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0924
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0925
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0926
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0927
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0928
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0929

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_092 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 92 + i)) (500 * (10 * 92 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0920
  by_cases h1 : i = 1
  · subst i
    exact chunk_0921
  by_cases h2 : i = 2
  · subst i
    exact chunk_0922
  by_cases h3 : i = 3
  · subst i
    exact chunk_0923
  by_cases h4 : i = 4
  · subst i
    exact chunk_0924
  by_cases h5 : i = 5
  · subst i
    exact chunk_0925
  by_cases h6 : i = 6
  · subst i
    exact chunk_0926
  by_cases h7 : i = 7
  · subst i
    exact chunk_0927
  by_cases h8 : i = 8
  · subst i
    exact chunk_0928
  by_cases h9 : i = 9
  · subst i
    exact chunk_0929
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
