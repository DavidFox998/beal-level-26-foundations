import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0480
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0481
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0482
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0483
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0484
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0485
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0486
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0487
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0488
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0489

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_048 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 48 + i)) (500 * (10 * 48 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0480
  by_cases h1 : i = 1
  · subst i
    exact chunk_0481
  by_cases h2 : i = 2
  · subst i
    exact chunk_0482
  by_cases h3 : i = 3
  · subst i
    exact chunk_0483
  by_cases h4 : i = 4
  · subst i
    exact chunk_0484
  by_cases h5 : i = 5
  · subst i
    exact chunk_0485
  by_cases h6 : i = 6
  · subst i
    exact chunk_0486
  by_cases h7 : i = 7
  · subst i
    exact chunk_0487
  by_cases h8 : i = 8
  · subst i
    exact chunk_0488
  by_cases h9 : i = 9
  · subst i
    exact chunk_0489
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
