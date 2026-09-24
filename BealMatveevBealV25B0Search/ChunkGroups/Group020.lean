import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0200
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0201
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0202
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0203
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0204
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0205
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0206
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0207
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0208
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0209

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_020 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 20 + i)) (500 * (10 * 20 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0200
  by_cases h1 : i = 1
  · subst i
    exact chunk_0201
  by_cases h2 : i = 2
  · subst i
    exact chunk_0202
  by_cases h3 : i = 3
  · subst i
    exact chunk_0203
  by_cases h4 : i = 4
  · subst i
    exact chunk_0204
  by_cases h5 : i = 5
  · subst i
    exact chunk_0205
  by_cases h6 : i = 6
  · subst i
    exact chunk_0206
  by_cases h7 : i = 7
  · subst i
    exact chunk_0207
  by_cases h8 : i = 8
  · subst i
    exact chunk_0208
  by_cases h9 : i = 9
  · subst i
    exact chunk_0209
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
