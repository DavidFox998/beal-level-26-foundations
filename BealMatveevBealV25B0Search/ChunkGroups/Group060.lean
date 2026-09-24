import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0600
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0601
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0602
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0603
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0604
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0605
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0606
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0607
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0608
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0609

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_060 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 60 + i)) (500 * (10 * 60 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0600
  by_cases h1 : i = 1
  · subst i
    exact chunk_0601
  by_cases h2 : i = 2
  · subst i
    exact chunk_0602
  by_cases h3 : i = 3
  · subst i
    exact chunk_0603
  by_cases h4 : i = 4
  · subst i
    exact chunk_0604
  by_cases h5 : i = 5
  · subst i
    exact chunk_0605
  by_cases h6 : i = 6
  · subst i
    exact chunk_0606
  by_cases h7 : i = 7
  · subst i
    exact chunk_0607
  by_cases h8 : i = 8
  · subst i
    exact chunk_0608
  by_cases h9 : i = 9
  · subst i
    exact chunk_0609
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
