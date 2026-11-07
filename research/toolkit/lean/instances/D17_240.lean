import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 240 of the cap-17 certificate: slots 122880 .. 123391 -/
theorem chk_240 : chunkCheck 17 T stdSt 122880 512 = true := by decide +kernel

end Row17
