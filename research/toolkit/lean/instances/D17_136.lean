import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 136 of the cap-17 certificate: slots 69632 .. 70143 -/
theorem chk_136 : chunkCheck 17 T stdSt 69632 512 = true := by decide +kernel

end Row17
