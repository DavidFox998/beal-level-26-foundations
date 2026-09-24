import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0250
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0251
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0252
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0253
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0254
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0255
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0256
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0257
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0258
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0259

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_025 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 25 + i)) (500 * (10 * 25 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0250
  by_cases h1 : i = 1
  · subst i
    exact chunk_0251
  by_cases h2 : i = 2
  · subst i
    exact chunk_0252
  by_cases h3 : i = 3
  · subst i
    exact chunk_0253
  by_cases h4 : i = 4
  · subst i
    exact chunk_0254
  by_cases h5 : i = 5
  · subst i
    exact chunk_0255
  by_cases h6 : i = 6
  · subst i
    exact chunk_0256
  by_cases h7 : i = 7
  · subst i
    exact chunk_0257
  by_cases h8 : i = 8
  · subst i
    exact chunk_0258
  by_cases h9 : i = 9
  · subst i
    exact chunk_0259
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
