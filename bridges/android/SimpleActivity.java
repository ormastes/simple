// SimpleActivity.java — Android bridge for Simple applications
//
// Minimal Android activity that loads the Simple shared library (.so)
// and calls app_main() via JNI.
//
// Usage:
//   1. Compile Simple app to shared library (.so) with android-arm64 preset
//   2. Place .so in app/src/main/jniLibs/arm64-v8a/
//   3. Set this activity as the launcher in AndroidManifest.xml
//
// The Simple runtime exports:
//   JNIEXPORT jint JNICALL Java_simple_SimpleActivity_nativeAppMain(
//       JNIEnv* env, jobject thiz, jobjectArray args);

package simple;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;

public class SimpleActivity extends Activity {
    private static final String TAG = "SimpleApp";

    // Load the Simple shared library
    static {
        System.loadLibrary("simple_app");
    }

    // Native method — implemented by JNI bridge
    private native int nativeAppMain(String[] args);

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        // Collect arguments from intent extras (if any)
        String[] args = new String[0];
        Bundle extras = getIntent().getExtras();
        if (extras != null && extras.containsKey("args")) {
            args = extras.getStringArray("args");
            if (args == null) {
                args = new String[0];
            }
        }

        Log.i(TAG, "Starting Simple app with " + args.length + " args");

        // Run the Simple app on a background thread to avoid blocking UI
        final String[] finalArgs = args;
        new Thread(() -> {
            int exitCode = nativeAppMain(finalArgs);
            Log.i(TAG, "Simple app exited with code: " + exitCode);
            if (exitCode != 0) {
                runOnUiThread(() -> finish());
            }
        }).start();
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        // Simple app shutdown is handled by the runtime
    }
}
