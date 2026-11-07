import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 245 of the cap-16 certificate: slots 250880 .. 251903 -/
theorem chk_245 : chunkCheck 16 T stdSt 250880 1024 = true := by decide +kernel

end Row16
