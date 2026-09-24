import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0460
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0461
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0462
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0463
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0464
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0465
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0466
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0467
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0468
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0469

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_046 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 46 + i)) (500 * (10 * 46 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0460
  by_cases h1 : i = 1
  · subst i
    exact chunk_0461
  by_cases h2 : i = 2
  · subst i
    exact chunk_0462
  by_cases h3 : i = 3
  · subst i
    exact chunk_0463
  by_cases h4 : i = 4
  · subst i
    exact chunk_0464
  by_cases h5 : i = 5
  · subst i
    exact chunk_0465
  by_cases h6 : i = 6
  · subst i
    exact chunk_0466
  by_cases h7 : i = 7
  · subst i
    exact chunk_0467
  by_cases h8 : i = 8
  · subst i
    exact chunk_0468
  by_cases h9 : i = 9
  · subst i
    exact chunk_0469
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
