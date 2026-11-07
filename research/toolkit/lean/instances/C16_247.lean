import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 247 of the cap-16 certificate: slots 252928 .. 253951 -/
theorem chk_247 : chunkCheck 16 T stdSt 252928 1024 = true := by decide +kernel

end Row16
