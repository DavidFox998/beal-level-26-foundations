import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0500
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0501
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0502
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0503
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0504
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0505
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0506
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0507
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0508
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0509

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_050 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 50 + i)) (500 * (10 * 50 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0500
  by_cases h1 : i = 1
  · subst i
    exact chunk_0501
  by_cases h2 : i = 2
  · subst i
    exact chunk_0502
  by_cases h3 : i = 3
  · subst i
    exact chunk_0503
  by_cases h4 : i = 4
  · subst i
    exact chunk_0504
  by_cases h5 : i = 5
  · subst i
    exact chunk_0505
  by_cases h6 : i = 6
  · subst i
    exact chunk_0506
  by_cases h7 : i = 7
  · subst i
    exact chunk_0507
  by_cases h8 : i = 8
  · subst i
    exact chunk_0508
  by_cases h9 : i = 9
  · subst i
    exact chunk_0509
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
