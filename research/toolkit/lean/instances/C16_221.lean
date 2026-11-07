import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 221 of the cap-16 certificate: slots 226304 .. 227327 -/
theorem chk_221 : chunkCheck 16 T stdSt 226304 1024 = true := by decide +kernel

end Row16
