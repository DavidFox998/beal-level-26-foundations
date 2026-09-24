import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0110
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0111
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0112
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0113
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0114
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0115
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0116
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0117
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0118
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0119

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_011 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 11 + i)) (500 * (10 * 11 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0110
  by_cases h1 : i = 1
  · subst i
    exact chunk_0111
  by_cases h2 : i = 2
  · subst i
    exact chunk_0112
  by_cases h3 : i = 3
  · subst i
    exact chunk_0113
  by_cases h4 : i = 4
  · subst i
    exact chunk_0114
  by_cases h5 : i = 5
  · subst i
    exact chunk_0115
  by_cases h6 : i = 6
  · subst i
    exact chunk_0116
  by_cases h7 : i = 7
  · subst i
    exact chunk_0117
  by_cases h8 : i = 8
  · subst i
    exact chunk_0118
  by_cases h9 : i = 9
  · subst i
    exact chunk_0119
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
