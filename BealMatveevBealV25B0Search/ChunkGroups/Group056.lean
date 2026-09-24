import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0560
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0561
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0562
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0563
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0564
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0565
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0566
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0567
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0568
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0569

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_056 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 56 + i)) (500 * (10 * 56 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0560
  by_cases h1 : i = 1
  · subst i
    exact chunk_0561
  by_cases h2 : i = 2
  · subst i
    exact chunk_0562
  by_cases h3 : i = 3
  · subst i
    exact chunk_0563
  by_cases h4 : i = 4
  · subst i
    exact chunk_0564
  by_cases h5 : i = 5
  · subst i
    exact chunk_0565
  by_cases h6 : i = 6
  · subst i
    exact chunk_0566
  by_cases h7 : i = 7
  · subst i
    exact chunk_0567
  by_cases h8 : i = 8
  · subst i
    exact chunk_0568
  by_cases h9 : i = 9
  · subst i
    exact chunk_0569
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
