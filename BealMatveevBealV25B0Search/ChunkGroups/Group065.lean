import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0650
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0651
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0652
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0653
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0654
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0655
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0656
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0657
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0658
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0659

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_065 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 65 + i)) (500 * (10 * 65 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0650
  by_cases h1 : i = 1
  · subst i
    exact chunk_0651
  by_cases h2 : i = 2
  · subst i
    exact chunk_0652
  by_cases h3 : i = 3
  · subst i
    exact chunk_0653
  by_cases h4 : i = 4
  · subst i
    exact chunk_0654
  by_cases h5 : i = 5
  · subst i
    exact chunk_0655
  by_cases h6 : i = 6
  · subst i
    exact chunk_0656
  by_cases h7 : i = 7
  · subst i
    exact chunk_0657
  by_cases h8 : i = 8
  · subst i
    exact chunk_0658
  by_cases h9 : i = 9
  · subst i
    exact chunk_0659
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
