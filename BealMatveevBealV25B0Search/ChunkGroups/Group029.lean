import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0290
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0291
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0292
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0293
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0294
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0295
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0296
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0297
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0298
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0299

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_029 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 29 + i)) (500 * (10 * 29 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0290
  by_cases h1 : i = 1
  · subst i
    exact chunk_0291
  by_cases h2 : i = 2
  · subst i
    exact chunk_0292
  by_cases h3 : i = 3
  · subst i
    exact chunk_0293
  by_cases h4 : i = 4
  · subst i
    exact chunk_0294
  by_cases h5 : i = 5
  · subst i
    exact chunk_0295
  by_cases h6 : i = 6
  · subst i
    exact chunk_0296
  by_cases h7 : i = 7
  · subst i
    exact chunk_0297
  by_cases h8 : i = 8
  · subst i
    exact chunk_0298
  by_cases h9 : i = 9
  · subst i
    exact chunk_0299
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
