import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0800
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0801
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0802
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0803
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0804
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0805
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0806
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0807
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0808
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0809

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_080 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 80 + i)) (500 * (10 * 80 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0800
  by_cases h1 : i = 1
  · subst i
    exact chunk_0801
  by_cases h2 : i = 2
  · subst i
    exact chunk_0802
  by_cases h3 : i = 3
  · subst i
    exact chunk_0803
  by_cases h4 : i = 4
  · subst i
    exact chunk_0804
  by_cases h5 : i = 5
  · subst i
    exact chunk_0805
  by_cases h6 : i = 6
  · subst i
    exact chunk_0806
  by_cases h7 : i = 7
  · subst i
    exact chunk_0807
  by_cases h8 : i = 8
  · subst i
    exact chunk_0808
  by_cases h9 : i = 9
  · subst i
    exact chunk_0809
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
