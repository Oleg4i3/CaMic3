package com.simplecam;

import android.Manifest;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.content.Context;
import android.content.pm.PackageManager;
import android.graphics.*;
import android.graphics.drawable.GradientDrawable;
import android.hardware.camera2.*;
import android.hardware.camera2.params.MeteringRectangle;
import android.media.*;
import android.media.MediaCodecInfo.CodecCapabilities;
import android.media.MediaCodecInfo.CodecProfileLevel;
import android.os.*;
import android.view.*;
import android.widget.*;
import android.content.ContentValues;
import android.net.Uri;
import android.os.Environment;
import android.os.ParcelFileDescriptor;
import android.provider.MediaStore;
import android.media.AudioDeviceInfo;
import android.media.AudioManager;
import android.media.audiofx.AutomaticGainControl;
import android.media.audiofx.NoiseSuppressor;
import android.media.audiofx.AcousticEchoCanceler;
import android.graphics.SurfaceTexture;
import android.opengl.EGL14;
import android.opengl.EGLConfig;
import android.opengl.EGLContext;
import android.opengl.EGLDisplay;
import android.opengl.EGLExt;
import android.opengl.EGLSurface;
import android.opengl.GLES11Ext;
import android.opengl.GLES20;
import java.io.File;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.FloatBuffer;
import java.util.*;

public class MainActivity extends Activity implements SurfaceHolder.Callback {

    private static final int VIDEO_W = 1280;
    private static final int VIDEO_H = 720;
    private static final int VIDEO_BPS_DEFAULT = 6_000_000;
    private static final int VIDEO_FPS = 30;
    private static final int AUDIO_SR = 48000;
    private static final int REQ_PERMS = 1;
    private static final float MAX_ZOOM_SPEED = 0.08f;
    // EIS
    private static final float EIS_CROP   = 1.15f;
    private static final int   ANALYSIS_W = 640;
    private static final int   ANALYSIS_H = 360;
    private static final int   SEARCH_RAD = 24;
    private static final int   TMPL_DIV   = 5; // шаблон = 1/5 кадра

    // UI
    private SurfaceView mSv;
    private Spinner mSpinner;
    private VerticalSeekBar mSeekGain;
    private FocusDrumView mFocusDrum;
    private TextView mTvGain, mTvStatus, mTvFocus;
    private Button mBtn, mSrcToggleBtn, mBtnPause;
    private volatile boolean mPaused = false;
    private long mPauseStartNano = 0L, mPauseEndNano = 0L;
    private GradientDrawable mBtnBgPause;
    private VuMeterView mVu;
    private OscilloscopeView mOscilloscope;
    private EnvelopeView mEnvelope;
    private SpectrumView mSpectrum;
    private ZoomLeverView mZoomLever;
    private LinearLayout mAudioSrcPanel;
    private CheckBox mCbSoftClip, mCbManualFocus, mCbFocusAssist;
    private boolean mAudioSrcExpanded = false;
    private View mFocusColumn;
    private volatile float mSavedZoomBeforeAssist = 1f;
    private Handler mFocusAssistHandler;
    private GradientDrawable mBtnBgIdle, mBtnBgRec;

    // Camera2
    private CameraManager mCamMgr;
    private CameraDevice mCamDev;
    private CameraCaptureSession mCapSess;
    private HandlerThread mCamThread;
    private Handler mCamHandler;
    private boolean mSurfaceReady;
    private boolean mPermsOk;
    private int mSensorOrientation = 90;
    private Rect mSensorRect;
    private float mMaxZoom = 1f;
    private volatile float mZoomLevel = 1f;
    private volatile float mZoomLeverPos = 0f;
    private volatile boolean mManualFocus = false;
    private volatile float mFocusValue = 0f;
    private float mMinFocusDist = 0f;

    // Recording
    private volatile boolean mRecording;
    private volatile float mGain = 1f;
    private volatile boolean mSoftClip = false;
    private volatile int mAudChannels = 2;
    private MediaCodec mVidEnc, mAudEnc;
    private MediaMuxer mMuxer;
    private Surface mEncSurface;
    private AudioRecord mAudRec;
    private Thread mAudThread;
    private int mVidTrack = -1, mAudTrack = -1;
    private volatile boolean mMuxReady;
    private final Object mMuxLock = new Object();
    private Uri mPendingUri;
    private ParcelFileDescriptor mPfd;
    private final List<AudioSrcItem> mSrcList = new ArrayList<>();
    private volatile boolean mAudRunning;

    // Pre-buffer
    private static class EncodedFrame {
        final byte[] data; final long pts; final int flags;
        EncodedFrame(ByteBuffer src, MediaCodec.BufferInfo bi) {
            data = new byte[bi.size];
            src.position(bi.offset); src.get(data, 0, bi.size);
            pts = bi.presentationTimeUs; flags = bi.flags;
        }
        boolean isKey() { return (flags & MediaCodec.BUFFER_FLAG_KEY_FRAME) != 0; }
    }
    private final java.util.ArrayDeque<EncodedFrame> mVidRing = new java.util.ArrayDeque<>();
    private final java.util.ArrayDeque<EncodedFrame> mAudRing = new java.util.ArrayDeque<>();
    private final Object mVidRingLock = new Object();
    private final Object mAudRingLock = new Object();
    private volatile int mVidWriteMode = 0;
    private volatile int mAudWriteMode = 0;
    private volatile long mMuxBasePts  = 0L;
    private volatile MediaFormat mVidOutFmt = null;
    private volatile MediaFormat mAudOutFmt = null;
    private volatile boolean mVidLoopRunning = false;

    // Settings
    private volatile int  mVideoBps = VIDEO_BPS_DEFAULT;
    private volatile int  mPreBufSecs = 1;
    private volatile boolean mPreBufferEnabled = true;
    private volatile int  mEvComp = 0;
    private int mEvMin = -6, mEvMax = 6;
    private SeekBar mSeekEv;
    private TextView mTvEv;

    // EIS state
    private volatile boolean mEisEnabled   = false;
    private volatile float   mEisDriftSpeed = 0.05f;
    private EisGlRenderer    mEisRenderer;
    private ImageReader      mAnalysisReader;
    private HandlerThread    mEisAnalysisThread;
    private Handler          mEisAnalysisHandler;
    // template matching
    private byte[]  mEisTmpl;
    private int     mEisTmplW, mEisTmplH, mEisTmplIdealX, mEisTmplIdealY;
    private double  mEisVirtualX, mEisVirtualY;
    private double  mEisLastMatchX, mEisLastMatchY;
    private long    mEisLastNs;
    private boolean mEisTmplReady;
    // overlay rect for debug frame
    private EisOverlayView  mEisOverlay;
    private volatile float  mEisOvNx, mEisOvNy, mEisOvNw, mEisOvNh; // normalized 0..1

    // Zoom loop
    private final Runnable mZoomRunnable = new Runnable() {
        @Override public void run() {
            float lever = mZoomLeverPos;
            if (Math.abs(lever) > 0.02f) {
                float abs = Math.abs(lever);
                float speed = (float)((Math.exp(abs*3.0)-1.0)/(Math.exp(3.0)-1.0))
                              * MAX_ZOOM_SPEED * Math.signum(lever);
                mZoomLevel = Math.max(1f, Math.min(mMaxZoom, mZoomLevel + speed));
                buildAndSendRequest();
            }
            if (mCamHandler != null) mCamHandler.postDelayed(this, 33);
        }
    };

    // =========================================================================
    // Lifecycle
    // =========================================================================
    @Override
    protected void onCreate(Bundle saved) {
        super.onCreate(saved);
        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON |
                             WindowManager.LayoutParams.FLAG_FULLSCREEN);
        mFocusAssistHandler = new Handler(Looper.getMainLooper());
        setContentView(buildLayout());
        mCamMgr = (CameraManager) getSystemService(CAMERA_SERVICE);
        showAirplaneModeReminder();
        checkPerms();
    }
    @Override protected void onPause() {
        super.onPause();
        if (mRecording) mRecording = false;
    }
    @Override protected void onDestroy() {
        super.onDestroy();
        if (mCamHandler != null) mCamHandler.removeCallbacks(mZoomRunnable);
        mVidLoopRunning = false;
        stopAudio();
        finalizeMuxer();
        releaseEis();
        releaseGlAndEncoder();
        try{if(mCapSess!=null)mCapSess.close();}catch(Exception ignored){}
        try{if(mCamDev!=null)mCamDev.close();}catch(Exception ignored){}
        if(mCamThread!=null)mCamThread.quitSafely();
    }

    // =========================================================================
    // Layout
    // =========================================================================
    private View buildLayout() {
        FrameLayout root = new FrameLayout(this);
        root.setBackgroundColor(Color.BLACK);

        mSv = new SurfaceView(this) {
            @Override protected void onMeasure(int wMs, int hMs) {
                int w = MeasureSpec.getSize(wMs), h = MeasureSpec.getSize(hMs);
                int targetH = w * 9 / 16;
                if (targetH > h) {
                    super.onMeasure(MeasureSpec.makeMeasureSpec(h * 16 / 9, MeasureSpec.EXACTLY),
                                    MeasureSpec.makeMeasureSpec(h, MeasureSpec.EXACTLY));
                } else {
                    super.onMeasure(MeasureSpec.makeMeasureSpec(w, MeasureSpec.EXACTLY),
                                    MeasureSpec.makeMeasureSpec(targetH, MeasureSpec.EXACTLY));
                }
            }
        };
        mSv.getHolder().addCallback(this);
        FrameLayout.LayoutParams svLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
        svLP.gravity = Gravity.CENTER;
        root.addView(mSv, svLP);

        // EIS overlay
        mEisOverlay = new EisOverlayView(this);
        root.addView(mEisOverlay, new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

        mOscilloscope = new OscilloscopeView(this);
        FrameLayout.LayoutParams oscLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, dp(130));
        oscLP.gravity = Gravity.TOP|Gravity.LEFT; oscLP.leftMargin=dp(50);
        oscLP.rightMargin=dp(60); oscLP.topMargin=dp(6);
        root.addView(mOscilloscope, oscLP);
        mOscilloscope.setVisibility(View.GONE);

        mEnvelope = new EnvelopeView(this);
        FrameLayout.LayoutParams envLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, dp(130));
        envLP.gravity = Gravity.TOP|Gravity.LEFT; envLP.leftMargin=dp(50);
        envLP.rightMargin=dp(60); envLP.topMargin=dp(6);
        root.addView(mEnvelope, envLP);

        mBtnBgIdle  = makeOval(0xFFDDCC00);
        mBtnBgRec   = makeOval(0xFFCC1100);
        mBtnBgPause = makeOval(0xFF1155CC);

        LinearLayout outer = new LinearLayout(this);
        outer.setOrientation(LinearLayout.VERTICAL);
        root.addView(outer, mp_mp());

        FrameLayout content = new FrameLayout(this);
        outer.addView(content, new LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));

        // Gain slider
        mSeekGain = new VerticalSeekBar(this);
        mSeekGain.setMax(800); mSeekGain.setProgress(400);
        mSeekGain.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            public void onProgressChanged(SeekBar s, int p, boolean u) {
                float db = -20f + p * 40f / 800f;
                mGain = (float) Math.pow(10.0, db / 20.0);
                if (mTvGain != null) mTvGain.setText(String.format("%+.1f", db) + "dB");
            }
            public void onStartTrackingTouch(SeekBar s) {}
            public void onStopTrackingTouch(SeekBar s) {}
        });
        FrameLayout.LayoutParams gainLP = new FrameLayout.LayoutParams(
            dp(44), ViewGroup.LayoutParams.MATCH_PARENT);
        gainLP.gravity = Gravity.LEFT;
        root.addView(mSeekGain, gainLP);

        TextView tvGainLbl = smallLabel("GAIN");
        FrameLayout.LayoutParams gainLblLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        gainLblLP.gravity=Gravity.LEFT|Gravity.TOP; gainLblLP.leftMargin=dp(6); gainLblLP.topMargin=dp(4);
        root.addView(tvGainLbl, gainLblLP);

        mTvGain = smallLabel("+0.0dB");
        FrameLayout.LayoutParams gainValLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        gainValLP.gravity=Gravity.LEFT|Gravity.BOTTOM; gainValLP.leftMargin=dp(3); gainValLP.bottomMargin=dp(169);
        root.addView(mTvGain, gainValLP);

        mVu = new VuMeterView(this);
        FrameLayout.LayoutParams vuLP = new FrameLayout.LayoutParams(
            dp(14), ViewGroup.LayoutParams.MATCH_PARENT);
        vuLP.gravity=Gravity.LEFT; vuLP.leftMargin=dp(44);
        root.addView(mVu, vuLP);

        // Right column
        LinearLayout rightCol = new LinearLayout(this);
        rightCol.setOrientation(LinearLayout.HORIZONTAL);
        FrameLayout.LayoutParams rightColLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.MATCH_PARENT);
        rightColLP.gravity = Gravity.RIGHT;
        root.addView(rightCol, rightColLP);

        mFocusColumn = buildFocusColumn();
        mFocusColumn.setVisibility(View.GONE);
        rightCol.addView(mFocusColumn, new LinearLayout.LayoutParams(
            dp(44), ViewGroup.LayoutParams.MATCH_PARENT));

        mZoomLever = new ZoomLeverView(this);
        mZoomLever.setListener(pos -> mZoomLeverPos = pos);
        rightCol.addView(mZoomLever, new LinearLayout.LayoutParams(
            dp(54), ViewGroup.LayoutParams.MATCH_PARENT));

        // Bottom panel
        LinearLayout panel = new LinearLayout(this);
        panel.setOrientation(LinearLayout.VERTICAL);
        panel.setBackgroundColor(0x00000000);
        panel.setPadding(dp(62), dp(2), dp(8), dp(3));
        outer.addView(panel, new LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

        mSrcToggleBtn = new Button(this);
        mSrcToggleBtn.setText("⚙"); mSrcToggleBtn.setAllCaps(false);
        mSrcToggleBtn.setTextSize(28); mSrcToggleBtn.setTextColor(0xFFBBBBBB);
        mSrcToggleBtn.setBackground(null); mSrcToggleBtn.setPadding(0,0,dp(8),0);
        mSrcToggleBtn.setOnClickListener(v -> {
            mAudioSrcExpanded = !mAudioSrcExpanded;
            mAudioSrcPanel.setVisibility(mAudioSrcExpanded ? View.VISIBLE : View.GONE);
            mSrcToggleBtn.setText(mAudioSrcExpanded ? "⚙ ▴" : "⚙");
        });

        mTvStatus = new TextView(this);
        mTvStatus.setTextColor(0xFFAAAAAA); mTvStatus.setTextSize(11);
        mTvStatus.setText("Ready"); mTvStatus.setSingleLine(false); mTvStatus.setMaxLines(2);
        mTvStatus.setLayoutParams(new LinearLayout.LayoutParams(
            0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
        panel.addView(hrow(mSrcToggleBtn, mTvStatus));

        // ── Двухколоночная панель настроек ───────────────────────────────────
        // Левая колонка: ЗВУК   |   Правая колонка: КАРТИНКА
        mAudioSrcPanel = new LinearLayout(this);
        mAudioSrcPanel.setOrientation(LinearLayout.HORIZONTAL);
        mAudioSrcPanel.setVisibility(View.GONE);
        mAudioSrcPanel.setPadding(dp(4), dp(4), dp(4), dp(4));

        // ── ЛЕВАЯ колонка: звук ───────────────────────────────────────────
        LinearLayout colLeft = new LinearLayout(this);
        colLeft.setOrientation(LinearLayout.VERTICAL);
        colLeft.setBackgroundColor(0x22FFFFFF);
        colLeft.setPadding(dp(6), dp(4), dp(6), dp(4));
        LinearLayout.LayoutParams colLP = new LinearLayout.LayoutParams(0,
            ViewGroup.LayoutParams.WRAP_CONTENT, 1f);
        colLP.rightMargin = dp(4);
        mAudioSrcPanel.addView(colLeft, colLP);

        colLeft.addView(smallLabel("🎙 ЗВУК"));

        // Источник звука
        mSpinner = new Spinner(this);
        ArrayAdapter<String> ad = new ArrayAdapter<>(this,
            android.R.layout.simple_spinner_item, new ArrayList<String>());
        ad.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
        mSpinner.setAdapter(ad);
        mSpinner.setOnItemSelectedListener(new AdapterView.OnItemSelectedListener() {
            @Override public void onItemSelected(AdapterView<?> p, View v, int pos, long id) {
                if (!mRecording) { stopAudio(); startMonitor(); }
            }
            @Override public void onNothingSelected(AdapterView<?> p) {}
        });
        LinearLayout srcRow = new LinearLayout(this);
        srcRow.setOrientation(LinearLayout.HORIZONTAL); srcRow.setGravity(Gravity.CENTER_VERTICAL);
        srcRow.addView(smallLabel("Src:")); srcRow.addView(mSpinner);
        colLeft.addView(srcRow);

        // Soft clip
        mCbSoftClip = new CheckBox(this);
        mCbSoftClip.setText("Soft clip"); mCbSoftClip.setTextColor(0xCCCCCCCC);
        mCbSoftClip.setTextSize(12); mCbSoftClip.setChecked(true); mSoftClip = true;
        mCbSoftClip.setOnCheckedChangeListener((cb, checked) -> mSoftClip = checked);
        colLeft.addView(mCbSoftClip);

        // Осциллограф / огибающая
        CheckBox cbOsc = new CheckBox(this);
        cbOsc.setText("Осциллограф"); cbOsc.setTextColor(0xCCCCCCCC); cbOsc.setTextSize(12);
        cbOsc.setOnCheckedChangeListener((cb, checked) -> {
            if (mOscilloscope != null) mOscilloscope.setVisibility(checked ? View.VISIBLE : View.GONE);
            if (mEnvelope != null) mEnvelope.setVisibility(checked ? View.GONE : View.VISIBLE);
        });
        colLeft.addView(cbOsc);

        // Спектр
        CheckBox cbSpec = new CheckBox(this);
        cbSpec.setText("Спектр"); cbSpec.setTextColor(0xCCCCCCCC); cbSpec.setTextSize(12);
        cbSpec.setChecked(true);
        cbSpec.setOnCheckedChangeListener((cb, checked) -> {
            if (mSpectrum != null) mSpectrum.setVisibility(checked ? View.VISIBLE : View.GONE);
        });
        colLeft.addView(cbSpec);

        // Pre-buffer
        CheckBox cbPB = new CheckBox(this);
        cbPB.setText("Pre-buffer"); cbPB.setTextColor(0xCCCCCCCC); cbPB.setTextSize(12);
        cbPB.setChecked(true);
        cbPB.setOnCheckedChangeListener((cb, on) -> mPreBufferEnabled = on);
        colLeft.addView(cbPB);
        final TextView tvPBLen = smallLabel("1 s");
        SeekBar sbPB = new SeekBar(this);
        sbPB.setMax(4); sbPB.setProgress(0);
        sbPB.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            public void onProgressChanged(SeekBar s, int p, boolean u) {
                mPreBufSecs = p + 1; tvPBLen.setText(mPreBufSecs + " s");
            }
            public void onStartTrackingTouch(SeekBar s) {} public void onStopTrackingTouch(SeekBar s) {}
        });
        LinearLayout pbRow = new LinearLayout(this);
        pbRow.setOrientation(LinearLayout.HORIZONTAL); pbRow.setGravity(Gravity.CENTER_VERTICAL);
        pbRow.addView(sbPB, new LinearLayout.LayoutParams(0,
            ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
        pbRow.addView(tvPBLen);
        colLeft.addView(pbRow);

        // Битрейт
        String[] bpsL={"500k","1M","2M","3M","4M","6M✓","8M","12M"};
        int[] bpsV={500_000,1_000_000,2_000_000,3_000_000,4_000_000,6_000_000,8_000_000,12_000_000};
        Spinner spBps = new Spinner(this);
        ArrayAdapter<String> bpsAd = new ArrayAdapter<>(this,
            android.R.layout.simple_spinner_item, bpsL);
        bpsAd.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
        spBps.setAdapter(bpsAd); spBps.setSelection(5);
        spBps.setOnItemSelectedListener(new AdapterView.OnItemSelectedListener() {
            public void onItemSelected(AdapterView<?> p, View v, int pos, long id) { mVideoBps = bpsV[pos]; }
            public void onNothingSelected(AdapterView<?> p) {}
        });
        LinearLayout bpsRow = new LinearLayout(this);
        bpsRow.setOrientation(LinearLayout.HORIZONTAL); bpsRow.setGravity(Gravity.CENTER_VERTICAL);
        bpsRow.addView(smallLabel("Bps:")); bpsRow.addView(spBps);
        colLeft.addView(bpsRow);

        // ── ПРАВАЯ колонка: картинка ──────────────────────────────────────
        LinearLayout colRight = new LinearLayout(this);
        colRight.setOrientation(LinearLayout.VERTICAL);
        colRight.setBackgroundColor(0x22FFFFFF);
        colRight.setPadding(dp(6), dp(4), dp(6), dp(4));
        mAudioSrcPanel.addView(colRight, new LinearLayout.LayoutParams(0,
            ViewGroup.LayoutParams.WRAP_CONTENT, 1f));

        colRight.addView(smallLabel("🎥 КАРТИНКА"));

        // Ручной фокус
        mCbManualFocus = new CheckBox(this);
        mCbManualFocus.setText("Ручной фокус"); mCbManualFocus.setTextColor(0xCCCCCCCC);
        mCbManualFocus.setTextSize(12);
        mCbManualFocus.setOnCheckedChangeListener((cb, checked) -> {
            mManualFocus = checked;
            mFocusColumn.setVisibility(checked ? View.VISIBLE : View.GONE);
            if (mCbFocusAssist != null)
                mCbFocusAssist.setVisibility(checked ? View.VISIBLE : View.GONE);
            if (!checked && mFocusAssistHandler != null)
                mFocusAssistHandler.removeCallbacksAndMessages(null);
            if (mCamHandler != null) mCamHandler.post(this::buildAndSendRequest);
        });
        colRight.addView(mCbManualFocus);

        // Focus assist
        mCbFocusAssist = new CheckBox(this);
        mCbFocusAssist.setText("Zoom при фокусировке"); mCbFocusAssist.setTextColor(0xCCCCCCCC);
        mCbFocusAssist.setTextSize(12); mCbFocusAssist.setVisibility(View.GONE);
        colRight.addView(mCbFocusAssist);

        // EV
        mTvEv = smallLabel("EV  0");
        colRight.addView(mTvEv);
        mSeekEv = new SeekBar(this);
        mSeekEv.setMax(mEvMax - mEvMin); mSeekEv.setProgress(-mEvMin);
        mSeekEv.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            public void onProgressChanged(SeekBar s, int p, boolean u) {
                mEvComp = mEvMin + p; updateEvLabel(mEvComp);
                if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest);
            }
            public void onStartTrackingTouch(SeekBar s) {} public void onStopTrackingTouch(SeekBar s) {}
        });
        colRight.addView(mSeekEv);

        // EIS стабилизатор
        colRight.addView(smallLabel("— Стабилизатор —"));
        CheckBox cbEis = new CheckBox(this);
        cbEis.setText("EIS вкл"); cbEis.setTextColor(0xCCFFCC99); cbEis.setTextSize(12);
        colRight.addView(cbEis);

        final TextView tvDrift = smallLabel("Дрейф: 5%");
        tvDrift.setVisibility(View.GONE);
        colRight.addView(tvDrift);

        SeekBar sbDrift = new SeekBar(this);
        sbDrift.setMax(98); sbDrift.setProgress(4);
        sbDrift.setVisibility(View.GONE);
        sbDrift.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            public void onProgressChanged(SeekBar s, int p, boolean u) {
                mEisDriftSpeed = 0.01f + p * 0.01f;
                tvDrift.setText(String.format("Дрейф: %d%%", p + 1));
            }
            public void onStartTrackingTouch(SeekBar s) {} public void onStopTrackingTouch(SeekBar s) {}
        });
        colRight.addView(sbDrift);

        cbEis.setOnCheckedChangeListener((cb, on) -> {
            if (mRecording) { cb.setChecked(!on); return; }
            mEisEnabled = on;
            // Сброс шаблона чтобы захватился новый при следующем кадре
            mEisTmplReady = false; mEisTmpl = null; mEisLastNs = 0;
            mEisVirtualX = 0; mEisVirtualY = 0;
            // Сбрасываем offset в рендерере немедленно
            if (mEisRenderer != null) mEisRenderer.setOffset(0f, 0f);
            sbDrift.setVisibility(on ? View.VISIBLE : View.GONE);
            tvDrift.setVisibility(on ? View.VISIBLE : View.GONE);
            mEisOverlay.setVisibility(on ? View.VISIBLE : View.GONE);
            // НЕ перезапускаем сессию — GL рендерер работает всегда
        });
        mEisOverlay.setVisibility(View.GONE);

        panel.addView(mAudioSrcPanel);

        mSpectrum = new SpectrumView(this);
        LinearLayout.LayoutParams specLP = new LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, dp(72));
        specLP.rightMargin = dp(120);
        panel.addView(mSpectrum, specLP);

        int recSize=dp(68), recRight=dp(62), recBottom=dp(8);
        mBtn = new Button(this);
        mBtn.setText("REC"); mBtn.setTextColor(Color.WHITE); mBtn.setTextSize(13);
        mBtn.setBackground(mBtnBgIdle);
        mBtn.setOnClickListener(v -> onRecordClick());
        FrameLayout.LayoutParams recLP = new FrameLayout.LayoutParams(recSize, recSize);
        recLP.gravity=Gravity.BOTTOM|Gravity.RIGHT; recLP.rightMargin=recRight; recLP.bottomMargin=recBottom;
        root.addView(mBtn, recLP);

        mBtnPause = new Button(this);
        mBtnPause.setText("⏸"); mBtnPause.setTextColor(Color.WHITE); mBtnPause.setTextSize(16);
        mBtnPause.setBackground(mBtnBgPause); mBtnPause.setVisibility(View.GONE);
        mBtnPause.setOnClickListener(v -> onPauseClick());
        FrameLayout.LayoutParams pauseLP = new FrameLayout.LayoutParams(dp(44), dp(44));
        pauseLP.gravity=Gravity.BOTTOM|Gravity.RIGHT;
        pauseLP.rightMargin=recRight+(recSize-dp(44))/2;
        pauseLP.bottomMargin=recBottom+recSize+dp(6);
        root.addView(mBtnPause, pauseLP);

        return root;
    }

    private View buildFocusColumn() {
        FrameLayout col = new FrameLayout(this);
        col.setBackgroundColor(0x33000000);
        mFocusDrum = new FocusDrumView(this);
        mFocusDrum.setOnFocusChangeListener(value -> {
            mFocusValue = value; updateFocusLabel(value);
            if (mManualFocus && mCamHandler != null)
                mCamHandler.post(MainActivity.this::buildAndSendRequest);
        });
        mFocusDrum.setOnDrumScrollListener(new FocusDrumView.OnDrumScrollListener() {
            @Override public void onScrollStart() {
                if (mCbFocusAssist==null||!mCbFocusAssist.isChecked()) return;
                mFocusAssistHandler.removeCallbacksAndMessages(null);
                mSavedZoomBeforeAssist = mZoomLevel;
                mZoomLevel = Math.min(mMaxZoom, Math.max(mZoomLevel*3f, 4f));
                if (mCamHandler!=null) mCamHandler.post(MainActivity.this::buildAndSendRequest);
            }
            @Override public void onScrollStop() {
                if (mCbFocusAssist==null||!mCbFocusAssist.isChecked()) return;
                mFocusAssistHandler.removeCallbacksAndMessages(null);
                mFocusAssistHandler.postDelayed(() -> {
                    mZoomLevel = mSavedZoomBeforeAssist;
                    if (mCamHandler!=null) mCamHandler.post(MainActivity.this::buildAndSendRequest);
                }, 300);
            }
        });
        col.addView(mFocusDrum, new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        TextView tvTop = smallLabel("∞");
        FrameLayout.LayoutParams topLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        topLP.gravity=Gravity.TOP|Gravity.CENTER_HORIZONTAL; topLP.topMargin=dp(4);
        col.addView(tvTop, topLP);
        TextView tvBot = smallLabel("▲");
        FrameLayout.LayoutParams botLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        botLP.gravity=Gravity.BOTTOM|Gravity.CENTER_HORIZONTAL; botLP.bottomMargin=dp(4);
        col.addView(tvBot, botLP);
        mTvFocus = smallLabel("∞");
        FrameLayout.LayoutParams midLP = new FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        midLP.gravity=Gravity.CENTER;
        col.addView(mTvFocus, midLP);
        return col;
    }

    private void updateFocusLabel(float v) {
        if (mTvFocus == null) return;
        mTvFocus.setText(v < 0.005f ? "∞" : String.format("%.1f", v*mMinFocusDist)+"m⁻¹");
    }
    private void updateEvLabel(int ev) {
        if (mTvEv == null) return;
        runOnUiThread(() -> mTvEv.setText(ev==0 ? "EV  0" : String.format("EV %+d", ev)));
    }
    private GradientDrawable makeOval(int color) {
        GradientDrawable d = new GradientDrawable();
        d.setShape(GradientDrawable.OVAL); d.setColor(color); return d;
    }
    private TextView smallLabel(String t) {
        TextView v = new TextView(this); v.setText(t); v.setTextColor(0xCCCCCCCC);
        v.setTextSize(11); v.setBackgroundColor(0x88000000);
        v.setPadding(dp(3),dp(1),dp(3),dp(1)); return v;
    }
    private LinearLayout hrow(View... views) {
        LinearLayout ll = new LinearLayout(this);
        ll.setOrientation(LinearLayout.HORIZONTAL); ll.setGravity(Gravity.CENTER_VERTICAL);
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        lp.bottomMargin=dp(2); ll.setLayoutParams(lp);
        for (View v : views) {
            if (v.getLayoutParams()==null) v.setLayoutParams(new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT));
            ll.addView(v);
        }
        return ll;
    }
    private ViewGroup.LayoutParams mp_mp() {
        return new ViewGroup.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
    }
    private int dp(int x) {
        return Math.round(x * getResources().getDisplayMetrics().density);
    }

    private void showAirplaneModeReminder() {
        new android.app.AlertDialog.Builder(this)
            .setTitle("\u2708  Airplane Mode recommended")
            .setMessage("For distraction-free recording:\n\n" +
                "  \u2022  Turn on Airplane Mode\n\n" +
                "This prevents calls, notifications\n" +
                "and Wi-Fi interruptions during recording.\n\n" +
                "(Screen will stay on while the app is open.)")
            .setPositiveButton("Got it", null)
            .setNeutralButton("Open Settings", (d, w) -> {
                try { startActivity(new android.content.Intent(
                    android.provider.Settings.ACTION_AIRPLANE_MODE_SETTINGS));
                } catch (Exception ignored) {}
            }).show();
    }

    // =========================================================================
    // Permissions / Surface
    // =========================================================================
    private void checkPerms() {
        List<String> need = new ArrayList<>();
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED)
            need.add(Manifest.permission.CAMERA);
        if (checkSelfPermission(Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED)
            need.add(Manifest.permission.RECORD_AUDIO);
        if (need.isEmpty()) { mPermsOk=true; if(mSurfaceReady) openCamera(); }
        else requestPermissions(need.toArray(new String[0]), REQ_PERMS);
    }
    @Override public void onRequestPermissionsResult(int req, String[] perms, int[] res) {
        for (int r : res) { if(r!=PackageManager.PERMISSION_GRANTED){status("Permissions required");return;} }
        mPermsOk=true; if(mSurfaceReady) openCamera();
    }
    @Override public void surfaceCreated(SurfaceHolder h) { mSurfaceReady=true; if(mPermsOk) openCamera(); }
    @Override public void surfaceChanged(SurfaceHolder h, int f, int w, int t) {}
    @Override public void surfaceDestroyed(SurfaceHolder h) {
        mSurfaceReady=false;
        releaseGlAndEncoder();
    }

    // =========================================================================
    // Camera2 open
    // =========================================================================
    @SuppressLint("MissingPermission")
    private void openCamera() {
        if (mCamThread==null||!mCamThread.isAlive()) {
            mCamThread = new HandlerThread("cam"); mCamThread.start();
            mCamHandler = new Handler(mCamThread.getLooper());
        }
        try {
            String camId = null;
            for (String id : mCamMgr.getCameraIdList()) {
                CameraCharacteristics ch = mCamMgr.getCameraCharacteristics(id);
                Integer facing = ch.get(CameraCharacteristics.LENS_FACING);
                if (facing!=null && facing==CameraCharacteristics.LENS_FACING_BACK) {
                    camId = id;
                    Integer so = ch.get(CameraCharacteristics.SENSOR_ORIENTATION);
                    if (so!=null) mSensorOrientation=so;
                    Rect rect = ch.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE);
                    if (rect!=null) mSensorRect=rect;
                    Float maxZ = ch.get(CameraCharacteristics.SCALER_AVAILABLE_MAX_DIGITAL_ZOOM);
                    if (maxZ!=null) mMaxZoom=maxZ;
                    Float minF = ch.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE);
                    if (minF!=null) mMinFocusDist=minF;
                    android.util.Range<Integer> evR =
                        ch.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE);
                    if (evR!=null){mEvMin=evR.getLower();mEvMax=evR.getUpper();}
                    break;
                }
            }
            if (camId==null) camId = mCamMgr.getCameraIdList()[0];
            mCamMgr.openCamera(camId, new CameraDevice.StateCallback() {
                @Override public void onOpened(CameraDevice dev) {
                    mCamDev=dev;
                    // startPreview блокирует (initGL), поэтому НЕ на mCamHandler
                    new Thread(MainActivity.this::startPreview).start();
                    buildAudioSources();
                    mCamHandler.post(mZoomRunnable);
                    runOnUiThread(() -> {
                        if(mSeekEv!=null){mSeekEv.setMax(mEvMax-mEvMin);
                            mSeekEv.setProgress(-mEvMin);updateEvLabel(0);}
                    });
                }
                @Override public void onDisconnected(CameraDevice dev){dev.close();mCamDev=null;}
                @Override public void onError(CameraDevice dev,int e){dev.close();mCamDev=null;}
            }, mCamHandler);
        } catch (Exception e) { status("openCamera: "+e.getMessage()); }
    }

    // =========================================================================
    // startPreview — GL рендерер живёт всегда, сессия создаётся один раз.
    // Вызывается из фонового треда (НЕ mCamHandler) — initGL блокирует.
    // =========================================================================
    private void startPreview() {
        if (mCamDev==null||!mSurfaceReady) return;
        try {
            if (mCapSess!=null){mCapSess.close();mCapSess=null;}

            // Убиваем старый рендерер и энкодер, создаём свежие
            if (mEisRenderer != null) { mEisRenderer.release(); mEisRenderer = null; }
            mVidLoopRunning = false;
            if (mVidEnc!=null){try{mVidEnc.stop();mVidEnc.release();}catch(Exception ignored){}mVidEnc=null;}
            if (mEncSurface!=null){try{mEncSurface.release();}catch(Exception ignored){}mEncSurface=null;}
            mVidOutFmt=null;
            synchronized(mVidRingLock){mVidRing.clear();} mVidWriteMode=0;

            // Создаём энкодер → получаем свежий mEncSurface
            ensureEncoders();
            if (mEncSurface==null) { status("Encoder init failed"); return; }

            // GL рендерер: camera → SurfaceTexture → GLSL → SurfaceView + mEncSurface
            // initGL блокирует до готовности GL (ок, мы на фоновом треде)
            mEisRenderer = new EisGlRenderer(EIS_CROP, VIDEO_W, VIDEO_H);
            mEisRenderer.initGL(mSv.getHolder().getSurface(), mEncSurface);

            // ImageReader для анализа (всегда, EIS флаг решает использовать ли)
            ensureAnalysisReader();

            Surface camIn = mEisRenderer.getCameraInputSurface();
            if (camIn==null) { status("GL surface null"); return; }

            List<Surface> targets = new ArrayList<>();
            targets.add(camIn);
            targets.add(mAnalysisReader.getSurface());

            mCamDev.createCaptureSession(targets,
                new CameraCaptureSession.StateCallback() {
                    @Override public void onConfigured(CameraCaptureSession s) {
                        mCapSess=s; buildAndSendRequest();
                    }
                    @Override public void onConfigureFailed(CameraCaptureSession s) {
                        status("Session config failed");
                    }
                }, mCamHandler);
        } catch (Exception e) { status("startPreview: "+e.getMessage()); }
    }

    private void buildAndSendRequest() {
        CameraCaptureSession sess=mCapSess; CameraDevice dev=mCamDev;
        if (sess==null||dev==null||!mSurfaceReady) return;
        try {
            CaptureRequest.Builder rb = dev.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW);
            // Всегда пишем в GL-рендерер; он отдаёт кадры и в SurfaceView и в encoder
            if (mEisRenderer!=null) {
                Surface camIn = mEisRenderer.getCameraInputSurface();
                if (camIn!=null&&camIn.isValid()) rb.addTarget(camIn);
            }
            // ImageReader для анализа (всегда зарегистрирован в сессии)
            if (mAnalysisReader!=null) rb.addTarget(mAnalysisReader.getSurface());

            if (mManualFocus) {
                rb.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_OFF);
                rb.set(CaptureRequest.LENS_FOCUS_DISTANCE, mFocusValue*mMinFocusDist);
            } else {
                rb.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_VIDEO);
            }
            rb.set(CaptureRequest.CONTROL_AE_MODE, CaptureRequest.CONTROL_AE_MODE_ON);
            rb.set(CaptureRequest.CONTROL_AE_EXPOSURE_COMPENSATION, mEvComp);
            if (mSensorRect!=null) {
                int cW=Math.max(1,(int)(mSensorRect.width()/mZoomLevel));
                int cH=Math.max(1,(int)(mSensorRect.height()/mZoomLevel));
                int cX=mSensorRect.left+(mSensorRect.width()-cW)/2;
                int cY=mSensorRect.top+(mSensorRect.height()-cH)/2;
                rb.set(CaptureRequest.SCALER_CROP_REGION, new Rect(cX,cY,cX+cW,cY+cH));
            }
            sess.setRepeatingRequest(rb.build(), null, mCamHandler);
        } catch (Exception ignored) {}
    }

    // =========================================================================
    // REC / PAUSE
    // =========================================================================
    private void onPauseClick() {
        mPaused = !mPaused;
        if (mPaused) {
            mPauseStartNano=System.nanoTime(); mVidWriteMode=0; mAudWriteMode=0;
            synchronized(mVidRingLock){mVidRing.clear();} synchronized(mAudRingLock){mAudRing.clear();}
            mBtnPause.setText("▶"); mBtnPause.setBackground(makeOval(0xFF228833));
            status("⏸ Paused");
        } else {
            mPauseEndNano=System.nanoTime();
            mMuxBasePts += (mPauseEndNano-mPauseStartNano)/1000L;
            mVidWriteMode=2; mAudWriteMode=2;
            mBtnPause.setText("⏸"); mBtnPause.setBackground(mBtnBgPause);
            status("● REC (resumed)");
        }
    }
    private void onRecordClick() {
        if (mRecording) { mRecording=false; mBtn.setEnabled(false); status("Stopping…");
            new Thread(this::doStop).start();
        } else { mBtn.setEnabled(false); status("Starting…");
            new Thread(this::doStart).start(); }
    }

    // =========================================================================
    // Encoders
    // =========================================================================
    private synchronized void ensureEncoders() {
        if (mVidEnc==null||mEncSurface==null||!mEncSurface.isValid()) {
            try {
                if(mVidEnc!=null){try{mVidEnc.stop();mVidEnc.release();}catch(Exception e){}mVidEnc=null;}
                if(mEncSurface!=null){try{mEncSurface.release();}catch(Exception e){}mEncSurface=null;}
                MediaFormat vf=MediaFormat.createVideoFormat(MediaFormat.MIMETYPE_VIDEO_AVC,VIDEO_W,VIDEO_H);
                vf.setInteger(MediaFormat.KEY_BIT_RATE,mVideoBps);
                vf.setInteger(MediaFormat.KEY_FRAME_RATE,VIDEO_FPS);
                vf.setInteger(MediaFormat.KEY_I_FRAME_INTERVAL,1);
                vf.setInteger(MediaFormat.KEY_COLOR_FORMAT,CodecCapabilities.COLOR_FormatSurface);
                vf.setInteger(MediaFormat.KEY_PROFILE,CodecProfileLevel.AVCProfileBaseline);
                vf.setInteger(MediaFormat.KEY_LEVEL,CodecProfileLevel.AVCLevel31);
                mVidEnc=MediaCodec.createEncoderByType(MediaFormat.MIMETYPE_VIDEO_AVC);
                mVidEnc.configure(vf,null,null,MediaCodec.CONFIGURE_FLAG_ENCODE);
                mEncSurface=mVidEnc.createInputSurface();
                mVidEnc.start(); mVidOutFmt=null;
                synchronized(mVidRingLock){mVidRing.clear();} mVidWriteMode=0;
            } catch(Exception e){status("VidEnc err: "+e.getMessage());return;}
        }
        if (!mVidLoopRunning) {
            Thread t=new Thread(this::videoPreviewLoop,"vid-preview"); t.setDaemon(true); t.start();
        }
    }

    private void videoPreviewLoop() {
        mVidLoopRunning=true;
        MediaCodec.BufferInfo info=new MediaCodec.BufferInfo();
        while (mVidLoopRunning) {
            MediaCodec enc=mVidEnc;
            if (enc==null){try{Thread.sleep(20);}catch(Exception e){}continue;}
            int out;
            try{out=enc.dequeueOutputBuffer(info,40_000);}catch(Exception e){break;}
            if (out==MediaCodec.INFO_OUTPUT_FORMAT_CHANGED){
                synchronized(mVidRingLock){mVidOutFmt=enc.getOutputFormat();} continue;}
            if (out<0) continue;
            try {
                boolean cfg=(info.flags&MediaCodec.BUFFER_FLAG_CODEC_CONFIG)!=0;
                if (cfg||info.size<=0) continue;
                ByteBuffer data=enc.getOutputBuffer(out);
                int mode=mVidWriteMode;
                if (mode==0) {
                    EncodedFrame f=new EncodedFrame(data,info);
                    synchronized(mVidRingLock){
                        mVidRing.addLast(f);
                        while(mVidRing.size()>1){
                            long span=mVidRing.peekLast().pts-mVidRing.peekFirst().pts;
                            if(span<=(long)mPreBufSecs*1_200_000L) break;
                            mVidRing.removeFirst();
                        }
                    }
                } else if (mode==1) {
                    synchronized(mVidRingLock){
                        boolean fk=false;
                        for(EncodedFrame rf:mVidRing){
                            if(!fk&&!rf.isKey()) continue; fk=true;
                            ByteBuffer rb=ByteBuffer.wrap(rf.data);
                            MediaCodec.BufferInfo bi=new MediaCodec.BufferInfo();
                            bi.set(0,rf.data.length,rf.pts-mMuxBasePts,rf.flags);
                            synchronized(mMuxLock){if(mMuxReady)mMuxer.writeSampleData(mVidTrack,rb,bi);}
                        }
                        mVidRing.clear();
                    }
                    MediaCodec.BufferInfo n=new MediaCodec.BufferInfo();
                    n.set(info.offset,info.size,info.presentationTimeUs-mMuxBasePts,info.flags);
                    synchronized(mMuxLock){if(mMuxReady)mMuxer.writeSampleData(mVidTrack,data,n);}
                    mVidWriteMode=2;
                } else {
                    MediaCodec.BufferInfo n=new MediaCodec.BufferInfo();
                    n.set(info.offset,info.size,info.presentationTimeUs-mMuxBasePts,info.flags);
                    synchronized(mMuxLock){if(mMuxReady)mMuxer.writeSampleData(mVidTrack,data,n);}
                }
            } finally {enc.releaseOutputBuffer(out,false);}
        }
        mVidLoopRunning=false;
    }

    // =========================================================================
    // Audio
    // =========================================================================
    @SuppressLint("MissingPermission")
    private void startMonitor() {
        if (mAudRunning||!mPermsOk) return;
        int pos=mSpinner.getSelectedItemPosition();
        AudioSrcItem src2=(pos>=0&&pos<mSrcList.size())?mSrcList.get(pos):null;
        int audioSrc=src2!=null?src2.audioSource:MediaRecorder.AudioSource.MIC;
        int chanCfg=AudioFormat.CHANNEL_IN_STEREO; int channels=2;
        int minBuf=AudioRecord.getMinBufferSize(AUDIO_SR,chanCfg,AudioFormat.ENCODING_PCM_16BIT);
        if(minBuf<=0){chanCfg=AudioFormat.CHANNEL_IN_MONO;channels=1;
            minBuf=AudioRecord.getMinBufferSize(AUDIO_SR,chanCfg,AudioFormat.ENCODING_PCM_16BIT);}
        int bufSize=Math.max(minBuf,AUDIO_SR*channels*2/5);
        AudioRecord rec=new AudioRecord(audioSrc,AUDIO_SR,chanCfg,AudioFormat.ENCODING_PCM_16BIT,bufSize);
        if(rec.getState()!=AudioRecord.STATE_INITIALIZED&&channels==2){
            rec.release();chanCfg=AudioFormat.CHANNEL_IN_MONO;channels=1;
            minBuf=AudioRecord.getMinBufferSize(AUDIO_SR,chanCfg,AudioFormat.ENCODING_PCM_16BIT);
            bufSize=Math.max(minBuf,AUDIO_SR*2/5);
            rec=new AudioRecord(audioSrc,AUDIO_SR,chanCfg,AudioFormat.ENCODING_PCM_16BIT,bufSize);}
        if(rec.getState()!=AudioRecord.STATE_INITIALIZED){rec.release();return;}
        if(Build.VERSION.SDK_INT>=23&&src2!=null&&src2.device!=null) rec.setPreferredDevice(src2.device);
        disableAudioEffects(rec.getAudioSessionId());
        mAudRec=rec; mAudChannels=channels;
        try {
            MediaFormat af=MediaFormat.createAudioFormat(MediaFormat.MIMETYPE_AUDIO_AAC,AUDIO_SR,channels);
            af.setInteger(MediaFormat.KEY_BIT_RATE,channels==1?192_000:320_000);
            af.setInteger(MediaFormat.KEY_AAC_PROFILE,CodecProfileLevel.AACObjectLC);
            mAudEnc=MediaCodec.createEncoderByType(MediaFormat.MIMETYPE_AUDIO_AAC);
            mAudEnc.configure(af,null,null,MediaCodec.CONFIGURE_FLAG_ENCODE);
            mAudEnc.start(); mAudOutFmt=null;
            synchronized(mAudRingLock){mAudRing.clear();} mAudWriteMode=0;
        } catch(Exception e){status("AudEnc err: "+e.getMessage());mAudEnc=null;}
        mAudRunning=true;
        mAudThread=new Thread(this::audioMainLoop,"aud-main"); mAudThread.setDaemon(true); mAudThread.start();
    }
    private void stopAudio(){
        mAudRunning=false;
        if(mAudRec!=null)try{mAudRec.stop();}catch(Exception ignored){}
        if(mAudThread!=null){try{mAudThread.join(600);}catch(Exception ignored){}mAudThread=null;}
        if(mAudRec!=null){try{mAudRec.release();}catch(Exception ignored){}mAudRec=null;}
        if(mAudEnc!=null){try{mAudEnc.stop();mAudEnc.release();}catch(Exception ignored){}mAudEnc=null;}
        mAudOutFmt=null; synchronized(mAudRingLock){mAudRing.clear();}
    }
    private void disableAudioEffects(int sid){
        try{if(AutomaticGainControl.isAvailable()){AutomaticGainControl a=AutomaticGainControl.create(sid);if(a!=null){a.setEnabled(false);a.release();}}}catch(Exception ignored){}
        try{if(NoiseSuppressor.isAvailable()){NoiseSuppressor n=NoiseSuppressor.create(sid);if(n!=null){n.setEnabled(false);n.release();}}}catch(Exception ignored){}
        try{if(AcousticEchoCanceler.isAvailable()){AcousticEchoCanceler e=AcousticEchoCanceler.create(sid);if(e!=null){e.setEnabled(false);e.release();}}}catch(Exception ignored){}
    }
    private void audioMainLoop(){
        final AudioRecord rec=mAudRec; final int ch=mAudChannels;
        final int chunkSamples=AUDIO_SR*ch/50; short[] buf=new short[chunkSamples];
        final long startUs=System.nanoTime()/1000L; long totalFrames=0L;
        rec.startRecording();
        while(mAudRunning){
            int r=rec.read(buf,0,chunkSamples); if(r<=0) continue;
            final float g=mGain; final boolean sc=mSoftClip; long sumSq=0;
            for(int i=0;i<r;i++){
                float s=buf[i]*g;
                if(sc){final float T=32768f*0.7f,knee=32768f-T;float ab=Math.abs(s);
                    if(ab>T)s=Math.signum(s)*(T+knee*(float)Math.tanh((ab-T)/knee));}
                if(s>32767f)s=32767f;else if(s<-32768f)s=-32768f;
                buf[i]=(short)s; sumSq+=(long)buf[i]*buf[i];
            }
            float peakAmp=0f;
            for(int i=0;i<r;i++){float a=Math.abs(buf[i])/32768f;if(a>peakAmp)peakAmp=a;}
            mVu.setPeak(peakAmp);
            mVu.setLevel((float)Math.sqrt((double)sumSq/r)/32768f);
            if(mOscilloscope!=null) mOscilloscope.pushSamples(buf,r,ch);
            if(mEnvelope!=null)     mEnvelope.pushSamples(buf,r,ch);
            if(mSpectrum!=null)     mSpectrum.pushSamples(buf,r,ch);
            MediaCodec enc=mAudEnc; if(enc==null) continue;
            long pts=startUs+totalFrames*1_000_000L/AUDIO_SR; totalFrames+=r/ch;
            int idx=enc.dequeueInputBuffer(5_000);
            if(idx>=0){ByteBuffer bb=enc.getInputBuffer(idx);bb.clear();
                for(int i=0;i<r;i++){bb.put((byte)(buf[i]&0xFF));bb.put((byte)(buf[i]>>8&0xFF));}
                enc.queueInputBuffer(idx,0,r*2,pts,0);}
            drainAudioEncoder(enc);
        }
        mVu.setLevel(0f); try{rec.stop();}catch(Exception ignored){}
    }
    private void drainAudioEncoder(MediaCodec enc){
        MediaCodec.BufferInfo info=new MediaCodec.BufferInfo();
        while(true){
            int out=enc.dequeueOutputBuffer(info,0);
            if(out==MediaCodec.INFO_OUTPUT_FORMAT_CHANGED){
                synchronized(mAudRingLock){mAudOutFmt=enc.getOutputFormat();}continue;}
            if(out<0) break;
            try{
                boolean cfg=(info.flags&MediaCodec.BUFFER_FLAG_CODEC_CONFIG)!=0;
                if(cfg||info.size<=0) continue;
                ByteBuffer data=enc.getOutputBuffer(out); int mode=mAudWriteMode;
                if(mode==0){
                    EncodedFrame f=new EncodedFrame(data,info);
                    synchronized(mAudRingLock){
                        mAudRing.addLast(f);
                        while(mAudRing.size()>1){
                            long span=mAudRing.peekLast().pts-mAudRing.peekFirst().pts;
                            if(span<=(long)mPreBufSecs*1_200_000L) break;
                            mAudRing.removeFirst();}
                    }
                } else if(mode==1){
                    synchronized(mAudRingLock){
                        boolean started=false;
                        for(EncodedFrame rf:mAudRing){
                            if(!started&&rf.pts<mMuxBasePts) continue; started=true;
                            ByteBuffer rb=ByteBuffer.wrap(rf.data);
                            MediaCodec.BufferInfo bi=new MediaCodec.BufferInfo();
                            bi.set(0,rf.data.length,rf.pts-mMuxBasePts,rf.flags);
                            synchronized(mMuxLock){if(mMuxReady)mMuxer.writeSampleData(mAudTrack,rb,bi);}
                        }
                        mAudRing.clear();
                    }
                    MediaCodec.BufferInfo n=new MediaCodec.BufferInfo();
                    n.set(info.offset,info.size,info.presentationTimeUs-mMuxBasePts,info.flags);
                    synchronized(mMuxLock){if(mMuxReady)mMuxer.writeSampleData(mAudTrack,data,n);}
                    mAudWriteMode=2;
                } else {
                    MediaCodec.BufferInfo n=new MediaCodec.BufferInfo();
                    n.set(info.offset,info.size,info.presentationTimeUs-mMuxBasePts,info.flags);
                    synchronized(mMuxLock){if(mMuxReady)mMuxer.writeSampleData(mAudTrack,data,n);}
                }
            } finally{enc.releaseOutputBuffer(out,false);}
            if((info.flags&MediaCodec.BUFFER_FLAG_END_OF_STREAM)!=0) break;
        }
    }

    // =========================================================================
    // doStart / doStop / finalizeMuxer
    // =========================================================================
    @SuppressLint("MissingPermission")
    private void doStart(){
        try{
            for(int w=0;w<40&&(mVidOutFmt==null||mAudOutFmt==null);w++) Thread.sleep(50);
            if(mVidOutFmt==null||mAudOutFmt==null){
                runOnUiThread(()->{mBtn.setEnabled(true);status("Encoder not ready — retry");}); return;}
            long basePts;
            synchronized(mVidRingLock){
                if(mPreBufferEnabled){
                    basePts=Long.MAX_VALUE;
                    for(EncodedFrame f:mVidRing){if(f.isKey()){basePts=f.pts;break;}}
                    if(basePts==Long.MAX_VALUE) basePts=0;
                } else { basePts=System.nanoTime()/1000L; }
            }
            mMuxBasePts=basePts;
            String displayPath;
            if(Build.VERSION.SDK_INT>=29){
                ContentValues cv=new ContentValues();
                cv.put(MediaStore.Video.Media.DISPLAY_NAME,"VID_"+System.currentTimeMillis()+".mp4");
                cv.put(MediaStore.Video.Media.MIME_TYPE,"video/mp4");
                cv.put(MediaStore.Video.Media.RELATIVE_PATH,"DCIM/CaMic");
                cv.put(MediaStore.Video.Media.IS_PENDING,1);
                mPendingUri=getContentResolver().insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI,cv);
                mPfd=getContentResolver().openFileDescriptor(mPendingUri,"rw");
                mMuxer=new MediaMuxer(mPfd.getFileDescriptor(),MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4);
                displayPath="DCIM/CaMic";
            } else {
                @SuppressWarnings("deprecation")
                File dir=new File(Environment.getExternalStoragePublicDirectory(
                    Environment.DIRECTORY_DCIM),"CaMic"); dir.mkdirs();
                File f=new File(dir,"VID_"+System.currentTimeMillis()+".mp4");
                mMuxer=new MediaMuxer(f.getAbsolutePath(),MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4);
                displayPath=f.getAbsolutePath();
            }
            @SuppressWarnings("deprecation")
            int rot=getWindowManager().getDefaultDisplay().getRotation()*90;
            mMuxer.setOrientationHint((mSensorOrientation-rot+360)%360);
            synchronized(mMuxLock){
                mVidTrack=mMuxer.addTrack(mVidOutFmt);
                mAudTrack=mMuxer.addTrack(mAudOutFmt);
                mMuxer.start(); mMuxReady=true;
            }
            mRecording=true;
            if(mPreBufferEnabled){mVidWriteMode=1;mAudWriteMode=1;}
            else{mVidWriteMode=2;mAudWriteMode=2;}
            final String fp=displayPath;
            runOnUiThread(()->{
                mBtn.setText("⏹ STOP");mBtn.setBackground(mBtnBgRec);mBtn.setEnabled(true);
                mBtnPause.setVisibility(View.VISIBLE);
                mBtnPause.setText("⏸");mBtnPause.setBackground(mBtnBgPause);
                mPaused=false; status("● REC  →  "+fp);
            });
        } catch(Exception e){
            mRecording=false;mVidWriteMode=0;mAudWriteMode=0; finalizeMuxer();
            runOnUiThread(()->{mBtn.setText("⏺ REC");mBtn.setBackground(mBtnBgIdle);
                mBtn.setEnabled(true);mBtnPause.setVisibility(View.GONE);status("Error: "+e.getMessage());});
        }
    }
    private void doStop(){
        try{Thread.sleep(200);}catch(Exception ignored){}
        mVidWriteMode=0;mAudWriteMode=0; finalizeMuxer();
    }
    private void finalizeMuxer(){
        synchronized(mMuxLock){
            try{if(mMuxer!=null){if(mMuxReady)mMuxer.stop();mMuxer.release();}}catch(Exception ignored){}
            mMuxer=null;mMuxReady=false;mVidTrack=-1;mAudTrack=-1;
        }
        try{if(mPfd!=null){mPfd.close();mPfd=null;}}catch(Exception ignored){}
        if(Build.VERSION.SDK_INT>=29&&mPendingUri!=null){
            ContentValues cv=new ContentValues();
            cv.put(MediaStore.Video.Media.IS_PENDING,0);
            getContentResolver().update(mPendingUri,cv,null,null); mPendingUri=null;
        }
        runOnUiThread(()->{mBtn.setText("⏺ REC");mBtn.setBackground(mBtnBgIdle);
            mBtn.setEnabled(true);mBtnPause.setVisibility(View.GONE);mPaused=false;status("Saved");});
    }
    private void status(String s){runOnUiThread(()->mTvStatus.setText(s));}

    // =========================================================================
    // Audio sources
    // =========================================================================
    private void buildAudioSources(){
        List<AudioSrcItem> list=new ArrayList<>();
        if(Build.VERSION.SDK_INT>=23){
            AudioManager am=(AudioManager)getSystemService(AUDIO_SERVICE);
            AudioDeviceInfo[] devs=am.getDevices(AudioManager.GET_DEVICES_INPUTS);
            boolean hasBuiltin=false;
            for(AudioDeviceInfo d:devs){
                int t=d.getType();
                if(t==AudioDeviceInfo.TYPE_BUILTIN_MIC){
                    if(hasBuiltin) continue; hasBuiltin=true;
                    list.add(new AudioSrcItem("Built-in mic",MediaRecorder.AudioSource.MIC,d));
                    if(Build.VERSION.SDK_INT>=24) list.add(new AudioSrcItem("Built-in mic (raw)",MediaRecorder.AudioSource.UNPROCESSED,d));
                } else if(t==AudioDeviceInfo.TYPE_USB_DEVICE||t==AudioDeviceInfo.TYPE_USB_HEADSET){
                    CharSequence pn=d.getProductName();
                    list.add(new AudioSrcItem("USB: "+(pn!=null&&pn.length()>0?pn:"audio"),MediaRecorder.AudioSource.MIC,d));
                } else if(t==AudioDeviceInfo.TYPE_WIRED_HEADSET){
                    list.add(new AudioSrcItem("Wired headset",MediaRecorder.AudioSource.MIC,d));
                } else if(t==AudioDeviceInfo.TYPE_BLUETOOTH_SCO){
                    list.add(new AudioSrcItem("Bluetooth mic",MediaRecorder.AudioSource.MIC,d));
                }
            }
        }
        if(list.isEmpty()){
            list.add(new AudioSrcItem("Default",MediaRecorder.AudioSource.DEFAULT,null));
            list.add(new AudioSrcItem("Microphone",MediaRecorder.AudioSource.MIC,null));
            list.add(new AudioSrcItem("Camcorder",MediaRecorder.AudioSource.CAMCORDER,null));
            list.add(new AudioSrcItem("Communication",MediaRecorder.AudioSource.VOICE_COMMUNICATION,null));
            if(Build.VERSION.SDK_INT>=24) list.add(new AudioSrcItem("Unprocessed (raw)",MediaRecorder.AudioSource.UNPROCESSED,null));
        }
        runOnUiThread(()->{
            mSrcList.clear(); mSrcList.addAll(list);
            List<String> names=new ArrayList<>(); for(AudioSrcItem i:mSrcList) names.add(i.name);
            @SuppressWarnings("unchecked") ArrayAdapter<String> ad2=(ArrayAdapter<String>)mSpinner.getAdapter();
            ad2.clear(); ad2.addAll(names); ad2.notifyDataSetChanged();
            int di=0;
            for(int i=0;i<mSrcList.size();i++){
                AudioSrcItem item=mSrcList.get(i);
                if(item.device!=null&&Build.VERSION.SDK_INT>=23){
                    int t=item.device.getType();
                    if(t==AudioDeviceInfo.TYPE_USB_DEVICE||t==AudioDeviceInfo.TYPE_USB_HEADSET){di=i;break;}
                }
            }
            if(di==0){for(int i=0;i<mSrcList.size();i++){if(mSrcList.get(i).audioSource==MediaRecorder.AudioSource.UNPROCESSED){di=i;break;}}}
            mSpinner.setSelection(di);
            if(!mRecording){stopAudio();startMonitor();}
        });
    }

    // =========================================================================
    // EIS — ImageReader и template matching (без OpenCV)
    // =========================================================================
    private void ensureAnalysisReader() {
        if (mEisAnalysisThread == null || !mEisAnalysisThread.isAlive()) {
            mEisAnalysisThread = new HandlerThread("eis-analysis");
            mEisAnalysisThread.start();
            mEisAnalysisHandler = new Handler(mEisAnalysisThread.getLooper());
        }
        if (mAnalysisReader != null) { mAnalysisReader.close(); mAnalysisReader = null; }
        mAnalysisReader = ImageReader.newInstance(ANALYSIS_W, ANALYSIS_H,
            android.graphics.ImageFormat.YUV_420_888, 2);
        mEisTmplReady = false;
        mAnalysisReader.setOnImageAvailableListener(reader -> {
            android.media.Image img = reader.acquireLatestImage();
            if (img == null) return;
            try { processEisFrame(img); } finally { img.close(); }
        }, mEisAnalysisHandler);
    }

    // processEisFrame — вызывается только из mEisAnalysisHandler
    // mEisTmpl защищён через mEisTmplReady (volatile) и локальную копию
    private void processEisFrame(android.media.Image img) {
        if (!mEisEnabled) return;

        android.media.Image.Plane plane = img.getPlanes()[0];
        int rowStride   = plane.getRowStride();
        int pixelStride = plane.getPixelStride();
        int W = img.getWidth(), H = img.getHeight();
        ByteBuffer yBuf = plane.getBuffer();

        // Плотный Y-массив W×H
        byte[] yFlat = new byte[W * H];
        for (int row = 0; row < H; row++) {
            int srcBase = row * rowStride, dstBase = row * W;
            for (int col = 0; col < W; col++) {
                int si = srcBase + col * pixelStride;
                yFlat[dstBase + col] = si < yBuf.limit() ? yBuf.get(si) : 0;
            }
        }

        long nowNs = System.nanoTime();
        double dt = mEisLastNs == 0 ? 0.033 : (nowNs - mEisLastNs) / 1e9;
        if (dt > 0.2) dt = 0.033;
        mEisLastNs = nowNs;

        int tmplW = W / TMPL_DIV, tmplH = H / TMPL_DIV;
        int idealX = (W - tmplW) / 2, idealY = (H - tmplH) / 2;

        // Берём локальную копию шаблона — защита от гонки с UI-тредом
        byte[] tmpl = mEisTmpl;
        if (!mEisTmplReady || tmpl == null) {
            tmpl = extractPatch(yFlat, W, idealX, idealY, tmplW, tmplH);
            mEisTmpl = tmpl;
            mEisTmplW = tmplW; mEisTmplH = tmplH;
            mEisLastMatchX = idealX; mEisLastMatchY = idealY;
            mEisVirtualX = idealX; mEisVirtualY = idealY;
            mEisTmplReady = true;
            updateOverlay(W, H, idealX, idealY, tmplW, tmplH);
            return;
        }

        // SAD поиск в окне ±SEARCH_RAD
        int lastX = (int)mEisLastMatchX, lastY = (int)mEisLastMatchY;
        int x0 = Math.max(0, lastX - SEARCH_RAD), y0 = Math.max(0, lastY - SEARCH_RAD);
        int x1 = Math.min(W - tmplW, lastX + SEARCH_RAD), y1 = Math.min(H - tmplH, lastY + SEARCH_RAD);
        long bestSad = Long.MAX_VALUE; int bestX = lastX, bestY = lastY;
        for (int sy = y0; sy <= y1; sy++) {
            for (int sx = x0; sx <= x1; sx++) {
                long sad = 0;
                outer:
                for (int ty = 0; ty < tmplH; ty++) {
                    int fi0 = (sy+ty)*W+sx, ti0 = ty*tmplW;
                    for (int tx = 0; tx < tmplW; tx++) {
                        sad += Math.abs((yFlat[fi0+tx]&0xFF)-(tmpl[ti0+tx]&0xFF));
                        if (sad >= bestSad) break outer;
                    }
                }
                if (sad < bestSad) { bestSad = sad; bestX = sx; bestY = sy; }
            }
        }

        // Потеря шаблона — перезахват и плавный откат
        boolean lost = bestSad > (long)(tmplW*tmplH)*50
            || bestX < 3 || bestX > W-tmplW-3 || bestY < 3 || bestY > H-tmplH-3;
        if (lost) {
            mEisTmpl = extractPatch(yFlat, W, idealX, idealY, tmplW, tmplH);
            bestX = idealX; bestY = idealY;
            mEisVirtualX += (idealX - mEisVirtualX) * 0.12;
            mEisVirtualY += (idealY - mEisVirtualY) * 0.12;
        }
        mEisLastMatchX = bestX; mEisLastMatchY = bestY;

        double driftFactor = Math.min(1.0, mEisDriftSpeed * dt * 30.0);
        mEisVirtualX += (bestX - mEisVirtualX) * driftFactor;
        mEisVirtualY += (bestY - mEisVirtualY) * driftFactor;

        // ST-матрица уже исправила оси — offset передаём прямо в display-пространстве
        float offX = (float)((bestX - mEisVirtualX) / W);
        float offY = (float)((bestY - mEisVirtualY) / H);
        float maxOff = (EIS_CROP - 1f) * 0.45f;
        offX = Math.max(-maxOff, Math.min(maxOff, offX));
        offY = Math.max(-maxOff, Math.min(maxOff, offY));

        EisGlRenderer r = mEisRenderer;
        if (r != null) r.setOffset(offX, offY);
        updateOverlay(W, H, bestX, bestY, tmplW, tmplH);
    }

    private byte[] extractPatch(byte[] src, int W, int x, int y, int pw, int ph) {
        byte[] p = new byte[pw * ph];
        for (int row = 0; row < ph; row++)
            System.arraycopy(src, (y+row)*W+x, p, row*pw, pw);
        return p;
    }

    private void updateOverlay(int W, int H, int rx, int ry, int rw, int rh) {
        mEisOvNx=(float)rx/W; mEisOvNy=(float)ry/H;
        mEisOvNw=(float)rw/W; mEisOvNh=(float)rh/H;
        if (mEisOverlay != null) mEisOverlay.postInvalidate();
    }

    private void releaseEis() {
        if (mAnalysisReader != null) { mAnalysisReader.close(); mAnalysisReader = null; }
        if (mEisAnalysisThread != null) {
            mEisAnalysisThread.quitSafely(); mEisAnalysisThread = null; mEisAnalysisHandler = null;
        }
        mEisTmplReady = false; mEisTmpl = null; mEisLastNs = 0;
    }

    /** Вызывается при onDestroy/surfaceDestroyed — безопасно вызывать дважды */
    private void releaseGlAndEncoder() {
        EisGlRenderer r = mEisRenderer; mEisRenderer = null;
        if (r != null) r.release();
        mVidLoopRunning = false;
        MediaCodec enc = mVidEnc; mVidEnc = null;
        if (enc!=null){try{enc.stop();enc.release();}catch(Exception ignored){}}
        Surface s = mEncSurface; mEncSurface = null;
        if (s!=null){try{s.release();}catch(Exception ignored){}}
    }

    // =========================================================================
    // EisGlRenderer
    // Единственный правильный порядок для Camera2 + OES:
    //   1. UV квад с V-флипом (0,1 внизу-слева) — компенсирует Y-флип ST-матрицы
    //   2. Crop + EIS-offset в screen UV пространстве
    //   3. ST-матрица переводит в OES-текстурные координаты
    //   gl_Position без вращения — сенсор уже выдаёт landscape кадры
    // =========================================================================
    private static class EisGlRenderer {

        private static final String VERT_SRC =
            "attribute vec4 aPos;\n" +
            "attribute vec2 aUv;\n" +
            "varying vec2 vUv;\n" +
            "uniform mat4 uSTMatrix;\n" +
            "uniform vec2 uOffset;\n" +
            "uniform float uCropInv;\n" +
            "void main(){\n" +
            "  gl_Position = aPos;\n" +
            // Шаг 1: crop + EIS offset в пространстве screen UV (до ST-матрицы)
            "  vec2 cropped = (aUv - 0.5) * uCropInv + 0.5 + uOffset;\n" +
            // Шаг 2: ST-матрица → OES texture coords (включает Y-флип)
            "  vUv = (uSTMatrix * vec4(cropped, 0.0, 1.0)).xy;\n" +
            "}\n";
        private static final String FRAG_SRC =
            "#extension GL_OES_EGL_image_external : require\n" +
            "precision mediump float;\n" +
            "varying vec2 vUv;\n" +
            "uniform samplerExternalOES uTex;\n" +
            "void main(){\n" +
            "  gl_FragColor = texture2D(uTex, vUv);\n" +
            "}\n";

        private final float mCropInv;
        private final int   mW, mH;

        // ── GL-поток ──────────────────────────────────────────────────────
        private HandlerThread mGlThread;
        private Handler       mGlHandler;

        // EGL
        private EGLDisplay mDisp;
        private EGLContext mCtx;
        private EGLSurface mPreviewSurf;
        private EGLSurface mEncSurf;

        // GL objects
        private SurfaceTexture mCamSt;
        private Surface        mCamSurface;
        private int mGlTex, mProg, mAPos, mAUv, mUSTMatrix, mUOffset, mUCropInv;
        private FloatBuffer mVtxBuf;
        private final float[] mSTMatrix = new float[16]; // от SurfaceTexture

        private volatile float mOffX, mOffY;
        private volatile boolean mReleased = false;

        EisGlRenderer(float eisCrop, int w, int h) {
            mCropInv = 1.0f / eisCrop;
            mW = w; mH = h;
        }

        /** Вызывается из любого потока; блокирует до завершения инициализации GL. */
        void initGL(Surface previewSurface, Surface encoderSurface) {
            mGlThread = new HandlerThread("eis-gl");
            mGlThread.start();
            mGlHandler = new Handler(mGlThread.getLooper());

            java.util.concurrent.CountDownLatch latch = new java.util.concurrent.CountDownLatch(1);
            mGlHandler.post(() -> {
                doInitGL(previewSurface, encoderSurface);
                latch.countDown();
            });
            try { latch.await(3, java.util.concurrent.TimeUnit.SECONDS); }
            catch (InterruptedException ignored) {}
        }

        private void doInitGL(Surface previewSurface, Surface encoderSurface) {
            // UV квад с V-флипом: (0,1) снизу-слева, (0,0) сверху-слева.
            // ST-матрица Camera2 содержит Y-флип — наш V-флип его компенсирует.
            // Итог: screen bottom-left → camera bottom-left (правильно).
            float[] verts = {
                -1f,-1f, 0f,1f,   // bottom-left  screen → UV(0,1)
                 1f,-1f, 1f,1f,   // bottom-right screen → UV(1,1)
                -1f, 1f, 0f,0f,   // top-left     screen → UV(0,0)
                 1f, 1f, 1f,0f,   // top-right    screen → UV(1,0)
            };
            mVtxBuf = ByteBuffer.allocateDirect(verts.length * 4)
                .order(ByteOrder.nativeOrder()).asFloatBuffer();
            mVtxBuf.put(verts).flip();

            mDisp = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY);
            EGL14.eglInitialize(mDisp, null, 0, null, 0);

            int[] attr = {
                EGL14.EGL_RED_SIZE,8, EGL14.EGL_GREEN_SIZE,8,
                EGL14.EGL_BLUE_SIZE,8, EGL14.EGL_ALPHA_SIZE,8,
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL14.EGL_SURFACE_TYPE, EGL14.EGL_WINDOW_BIT,
                0x3142, 1,   // EGL_RECORDABLE_ANDROID — нужно для encoder surface
                EGL14.EGL_NONE
            };
            EGLConfig[] cfgs = new EGLConfig[1]; int[] n = new int[1];
            EGL14.eglChooseConfig(mDisp, attr, 0, cfgs, 0, 1, n, 0);

            int[] ctxAttr = {EGL14.EGL_CONTEXT_CLIENT_VERSION, 2, EGL14.EGL_NONE};
            mCtx = EGL14.eglCreateContext(mDisp, cfgs[0], EGL14.EGL_NO_CONTEXT, ctxAttr, 0);

            int[] surfAttr = {EGL14.EGL_NONE};
            mPreviewSurf = EGL14.eglCreateWindowSurface(mDisp, cfgs[0], previewSurface, surfAttr, 0);
            mEncSurf     = EGL14.eglCreateWindowSurface(mDisp, cfgs[0], encoderSurface, surfAttr, 0);

            // Делаем контекст текущим на этом (GL) потоке — и не меняем
            EGL14.eglMakeCurrent(mDisp, mPreviewSurf, mPreviewSurf, mCtx);

            int[] tex = new int[1];
            GLES20.glGenTextures(1, tex, 0);
            mGlTex = tex[0];
            GLES20.glBindTexture(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, mGlTex);
            GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES,
                GLES20.GL_TEXTURE_MIN_FILTER, GLES20.GL_LINEAR);
            GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES,
                GLES20.GL_TEXTURE_MAG_FILTER, GLES20.GL_LINEAR);
            GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES,
                GLES20.GL_TEXTURE_WRAP_S, GLES20.GL_CLAMP_TO_EDGE);
            GLES20.glTexParameteri(GLES11Ext.GL_TEXTURE_EXTERNAL_OES,
                GLES20.GL_TEXTURE_WRAP_T, GLES20.GL_CLAMP_TO_EDGE);

            mCamSt = new SurfaceTexture(mGlTex);
            mCamSt.setDefaultBufferSize(mW, mH);

            // onFrameAvailableListener вызывается из камера-треда —
            // постим рендеринг на GL-тред, чтобы updateTexImage шёл там же
            mCamSt.setOnFrameAvailableListener(
                st -> { if (!mReleased && mGlHandler != null) mGlHandler.post(this::doRenderFrame); },
                mGlHandler   // listener тоже вызывается на GL-треде
            );
            mCamSurface = new Surface(mCamSt);

            mProg     = buildProgram(VERT_SRC, FRAG_SRC);
            mAPos     = GLES20.glGetAttribLocation(mProg,  "aPos");
            mAUv      = GLES20.glGetAttribLocation(mProg,  "aUv");
            mUSTMatrix= GLES20.glGetUniformLocation(mProg, "uSTMatrix");
            mUOffset  = GLES20.glGetUniformLocation(mProg, "uOffset");
            mUCropInv = GLES20.glGetUniformLocation(mProg, "uCropInv");
            // Инициализируем STMatrix единичной — будет перезаписана при первом кадре
            android.opengl.Matrix.setIdentityM(mSTMatrix, 0);
        }

        void setOffset(float nx, float ny) { mOffX = nx; mOffY = ny; }

        Surface getCameraInputSurface() { return mCamSurface; }

        /** Выполняется только на mGlThread. */
        private void doRenderFrame() {
            if (mReleased || mDisp == null || mCtx == null || mCamSt == null) return;
            // updateTexImage ОБЯЗАН быть на том же треде, где текущий EGL-контекст
            mCamSt.updateTexImage();
            // Получаем актуальную матрицу трансформации — она меняется каждый кадр
            mCamSt.getTransformMatrix(mSTMatrix);

            // Preview
            EGL14.eglMakeCurrent(mDisp, mPreviewSurf, mPreviewSurf, mCtx);
            GLES20.glViewport(0, 0, mW, mH);
            drawQuad();
            EGL14.eglSwapBuffers(mDisp, mPreviewSurf);

            // Encoder
            EGL14.eglMakeCurrent(mDisp, mEncSurf, mEncSurf, mCtx);
            GLES20.glViewport(0, 0, mW, mH);
            drawQuad();
            EGLExt.eglPresentationTimeANDROID(mDisp, mEncSurf, System.nanoTime());
            EGL14.eglSwapBuffers(mDisp, mEncSurf);
        }

        private void drawQuad() {
            GLES20.glUseProgram(mProg);
            GLES20.glBindTexture(GLES11Ext.GL_TEXTURE_EXTERNAL_OES, mGlTex);
            // Матрица от SurfaceTexture — исправляет поворот и зеркало OES-текстуры
            GLES20.glUniformMatrix4fv(mUSTMatrix, 1, false, mSTMatrix, 0);
            GLES20.glUniform2f(mUOffset, mOffX, mOffY);
            GLES20.glUniform1f(mUCropInv, mCropInv);
            mVtxBuf.position(0);
            GLES20.glVertexAttribPointer(mAPos, 2, GLES20.GL_FLOAT, false, 16, mVtxBuf);
            GLES20.glEnableVertexAttribArray(mAPos);
            mVtxBuf.position(2);
            GLES20.glVertexAttribPointer(mAUv, 2, GLES20.GL_FLOAT, false, 16, mVtxBuf);
            GLES20.glEnableVertexAttribArray(mAUv);
            GLES20.glDrawArrays(GLES20.GL_TRIANGLE_STRIP, 0, 4);
        }

        void release() {
            mReleased = true;
            if (mGlHandler != null) {
                // Освобождаем GL-ресурсы на GL-треде, потом останавливаем тред
                java.util.concurrent.CountDownLatch latch = new java.util.concurrent.CountDownLatch(1);
                mGlHandler.post(() -> { doReleaseGL(); latch.countDown(); });
                try { latch.await(2, java.util.concurrent.TimeUnit.SECONDS); } catch (Exception ignored) {}
            }
            if (mGlThread != null) { mGlThread.quitSafely(); mGlThread = null; }
            mGlHandler = null;
            if (mCamSurface != null) { mCamSurface.release(); mCamSurface = null; }
        }

        private void doReleaseGL() {
            if (mCamSt != null) { mCamSt.release(); mCamSt = null; }
            if (mDisp != null && mCtx != null) {
                EGL14.eglMakeCurrent(mDisp,
                    EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_CONTEXT);
                if (mPreviewSurf != null) EGL14.eglDestroySurface(mDisp, mPreviewSurf);
                if (mEncSurf != null)     EGL14.eglDestroySurface(mDisp, mEncSurf);
                EGL14.eglDestroyContext(mDisp, mCtx);
                EGL14.eglTerminate(mDisp);
                mDisp = null; mCtx = null;
            }
        }

        private static int buildProgram(String vert, String frag) {
            int vs = compileShader(GLES20.GL_VERTEX_SHADER, vert);
            int fs = compileShader(GLES20.GL_FRAGMENT_SHADER, frag);
            int prog = GLES20.glCreateProgram();
            GLES20.glAttachShader(prog, vs); GLES20.glAttachShader(prog, fs);
            GLES20.glLinkProgram(prog); return prog;
        }
        private static int compileShader(int type, String src) {
            int sh = GLES20.glCreateShader(type);
            GLES20.glShaderSource(sh, src); GLES20.glCompileShader(sh); return sh;
        }
    }

    // =========================================================================
    // EIS overlay — рисует рамку захваченного шаблона поверх превью
    // =========================================================================
    class EisOverlayView extends View {
        private final Paint mPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
        EisOverlayView(Context c) {
            super(c);
            mPaint.setStyle(Paint.Style.STROKE);
            mPaint.setColor(0xFFFF4444);
            mPaint.setStrokeWidth(3f);
        }
        @Override protected void onDraw(Canvas canvas) {
            if (!mEisEnabled) return;
            float w=getWidth(), h=getHeight();
            float rx = mEisOvNx * w, ry = mEisOvNy * h;
            float rw = mEisOvNw * w, rh = mEisOvNh * h;
            canvas.drawRect(rx, ry, rx+rw, ry+rh, mPaint);
            // Маленький крест в центре рамки
            float cx=rx+rw/2, cy=ry+rh/2, cs=dp(8);
            canvas.drawLine(cx-cs,cy,cx+cs,cy,mPaint);
            canvas.drawLine(cx,cy-cs,cx,cy+cs,mPaint);
        }
        private int dp(int x){ return Math.round(x*getResources().getDisplayMetrics().density); }
    }

	private static class AudioSrcItem {
		final String name;
		final int audioSource;
		final AudioDeviceInfo device;
		
		AudioSrcItem(String n, int s, AudioDeviceInfo d) {
			name = n;
			audioSource = s;
			device = d;
		}
	}
	
	static class VerticalSeekBar extends View {
		private int mMax = 100;
		private int mProgress = 0;
		
		private final Paint mTrackPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mFillPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mThumbPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mRidgePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		
		private SeekBar.OnSeekBarChangeListener mListener;
		
		VerticalSeekBar(Context c) {
			super(c);
			mTrackPaint.setColor(0x44FFFFFF);
			mFillPaint.setColor(0xFFDDCC00);
			mThumbPaint.setColor(0xFFEEEEEE);
			mRidgePaint.setColor(0xFF888866);
			mRidgePaint.setStyle(Paint.Style.STROKE);
			mRidgePaint.setStrokeWidth(1.2f * c.getResources().getDisplayMetrics().density);
			setClickable(true);
		}
		
		void setMax(int max) { mMax = max; invalidate(); }
		void setProgress(int p) { mProgress = Math.max(0, Math.min(mMax, p)); invalidate(); }
		int getMax() { return mMax; }
		int getProgress() { return mProgress; }
		void setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener l) { mListener = l; }

		// Высота ручки микшера в px
		private float faderH(float w) { return Math.round(w * 0.7f) + dp(20); }

		private int dp(int x) {
			return Math.round(x * getResources().getDisplayMetrics().density);
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			final float trackW = w * 0.3f;
			final float cx = w / 2f;
			final float trkX1 = cx - trackW / 2f;
			final float trkX2 = cx + trackW / 2f;
			final float halfFader = faderH(w) / 2f;
			final float padV = halfFader + 2f;
			final float trkT = padV;
			final float trkB = h - padV;
			final float trkH = trkB - trkT;

			float frac = mMax > 0 ? (float) mProgress / mMax : 0f;
			float thumbY = trkB - frac * trkH;

			// Трек
			canvas.drawRoundRect(new RectF(trkX1, trkT, trkX2, trkB),
				trackW / 2f, trackW / 2f, mTrackPaint);
			// Заполненная часть
			canvas.drawRoundRect(new RectF(trkX1, thumbY, trkX2, trkB),
				trackW / 2f, trackW / 2f, mFillPaint);
			// Метка 0 dB
			Paint z = new Paint(Paint.ANTI_ALIAS_FLAG);
			z.setColor(0x88FFFFFF); z.setStrokeWidth(1.5f);
			canvas.drawLine(trkX1 - 3f, trkB - 0.5f * trkH, trkX2 + 3f, trkB - 0.5f * trkH, z);

			// ── Ручка (fader cap) — широкий прямоугольник во всю ширину ──────
			float fH = faderH(w);
			float fW = w - 2f;
			RectF fader = new RectF(1f, thumbY - fH/2f, 1f + fW, thumbY + fH/2f);
			// Тень
			Paint shadow = new Paint(Paint.ANTI_ALIAS_FLAG);
			shadow.setColor(0x66000000);
			shadow.setStyle(Paint.Style.FILL);
			canvas.drawRoundRect(new RectF(fader.left+2, fader.top+3, fader.right+2, fader.bottom+3),
				dp(4), dp(4), shadow);
			// Тело ручки
			canvas.drawRoundRect(fader, dp(4), dp(4), mThumbPaint);
			// Горизонтальные риски (3 штуки по центру)
			float rInset = fW * 0.18f;
			for (int ri = -1; ri <= 1; ri++) {
				float ry = thumbY + ri * dp(4);
				canvas.drawLine(1f + rInset, ry, 1f + fW - rInset, ry, mRidgePaint);
			}
			// Центральная риска чуть длиннее и ярче
			Paint cLine = new Paint(Paint.ANTI_ALIAS_FLAG);
			cLine.setColor(0xFFDDCC00); cLine.setStrokeWidth(1.5f);
			canvas.drawLine(1f + rInset * 0.6f, thumbY, 1f + fW - rInset * 0.6f, thumbY, cLine);
		}
		
		@Override
		public boolean onTouchEvent(MotionEvent e) {
			if (!isEnabled()) return false;
			final float h = getHeight(), w = getWidth();
			final float halfFader = faderH(w) / 2f;
			final float padV = halfFader + 2f;
			final float trkT = padV;
			final float trkB = h - padV;
			final float trkH = trkB - trkT;
			
			switch (e.getAction()) {
				case MotionEvent.ACTION_DOWN:
				if (mListener != null) mListener.onStartTrackingTouch(null);
				// fall through
				case MotionEvent.ACTION_MOVE: {
					float frac = 1f - (e.getY() - trkT) / trkH;
					int p = Math.max(0, Math.min(mMax, Math.round(frac * mMax)));
					mProgress = p;
					invalidate();
					if (mListener != null) mListener.onProgressChanged(null, p, true);
					return true;
				}
				case MotionEvent.ACTION_UP:
				case MotionEvent.ACTION_CANCEL:
				if (mListener != null) mListener.onStopTrackingTouch(null);
				return true;
			}
			return false;
		}
	}
	
	// ─── Вертикальный VU-метр dBFS ───────────────────────────────────────────
	// Сегменты снизу вверх. Пик-маркер — горизонтальная черта с hold 1.8s.

	static class VuMeterView extends View {
		private static final int N = 30;
		private static final float MIN_DB = -60f;
		private static final long PEAK_HOLD_MS = 1800;

		private final Paint mSegPaint   = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mPeakPaint  = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mDbLblPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final RectF mRect       = new RectF();
		private float mLevelDb  = MIN_DB;
		private float mPeakDb   = MIN_DB;
		private long  mPeakHoldUntil = 0;

		VuMeterView(Context c) {
			super(c);
			mPeakPaint.setColor(0xFFFFFFFF);
			float vuDensity = c.getResources().getDisplayMetrics().density;
			mPeakPaint.setStrokeWidth(4f * vuDensity);
			mPeakPaint.setStyle(Paint.Style.STROKE);
			float density = c.getResources().getDisplayMetrics().density;
			mDbLblPaint.setTextSize(5.5f * density);
			mDbLblPaint.setTextAlign(Paint.Align.RIGHT);
			mDbLblPaint.setAntiAlias(true);
		}

		void setLevel(float rms) {
			mLevelDb = rms > 1e-6f ? Math.max(MIN_DB, (float)(20.0 * Math.log10(rms))) : MIN_DB;
			postInvalidate();
		}

		void setPeak(float peak) {
			float db = peak > 1e-6f ? Math.max(MIN_DB, (float)(20.0 * Math.log10(peak))) : MIN_DB;
			if (db >= mPeakDb || System.currentTimeMillis() > mPeakHoldUntil) {
				mPeakDb = db;
				mPeakHoldUntil = System.currentTimeMillis() + PEAK_HOLD_MS;
			}
		}

		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			final float segH = (h - N - 1f) / N;
			final float segW = w - 2f;

			for (int i = 0; i < N; i++) {
				float segDb = MIN_DB + (float) i / N * (-MIN_DB);
				boolean lit = mLevelDb >= segDb;
				int color;
				if (!lit)             color = 0xFF181818;
				else if (segDb < -12f) color = 0xFF00CC55;
				else if (segDb <  -6f) color = 0xFFFFBB00;
				else                   color = 0xFFFF2200;
				mSegPaint.setColor(color);
				float y = h - 1f - i * (segH + 1f) - segH;
				mRect.set(1f, y, 1f + segW, y + segH);
				canvas.drawRoundRect(mRect, 2f, 2f, mSegPaint);
			}

			// Пик-маркер
			if (mPeakDb > MIN_DB) {
				float frac = (mPeakDb - MIN_DB) / (-MIN_DB);
				float py = h - 1f - frac * (h - 2f);
				long now = System.currentTimeMillis();
				int peakColor;
				if      (mPeakDb >= -3f)  peakColor = 0xFFFF2200;
				else if (mPeakDb >= -12f) peakColor = 0xFFFFBB00;
				else                      peakColor = 0xFF00FF88;
				boolean fading = now > mPeakHoldUntil - 400;
				if (!fading || (now / 150) % 2 == 0) {
					mPeakPaint.setColor(peakColor);
					canvas.drawLine(0, py, w, py, mPeakPaint);
				}
			}

			// ── dB-метки поверх индикатора ────────────────────────────────────
			float[] dbMarks  = { 0f, -6f, -12f, -24f, -48f, -60f };
			String[] dbStrs  = { "0", "-6", "-12", "-24", "-48", "-60" };
			float lblAscent = -mDbLblPaint.ascent();
			for (int di = 0; di < dbMarks.length; di++) {
				float frac = (dbMarks[di] - MIN_DB) / (-MIN_DB);
				float ly   = h - 1f - frac * (h - 2f);
				// цвет совпадает с цветом сегмента
				if      (dbMarks[di] >= -6f)  mDbLblPaint.setColor(0xFFFF6644);
				else if (dbMarks[di] >= -12f) mDbLblPaint.setColor(0xFFFFDD44);
				else                          mDbLblPaint.setColor(0xCCBBFFCC);
				mDbLblPaint.setAlpha(200);
				// рисуем справа, сдвинув вверх на половину высоты шрифта
				canvas.drawText(dbStrs[di], w - 1f, ly + lblAscent * 0.5f, mDbLblPaint);
			}
		}
	}
	
	// ─── Рычаг зума ──────────────────────────────────────────────────────────
	
	static class ZoomLeverView extends View {
		interface Listener {
			void onLever(float pos);
		}
		
		private Listener mListener;
		private volatile float mPos = 0f;
		private boolean mTracking = false;
		private float trkT, trkB, trkH, trkW, mid, cx;
		
		private final Paint mTrackPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mThumbPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mMarkPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mTextPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		
		ZoomLeverView(Context c) {
			super(c);
			mTrackPaint.setColor(0x55FFFFFF);
			mThumbPaint.setColor(0xFFFFFFFF);
			mMarkPaint.setColor(0xAAFFFFFF);
			mMarkPaint.setStyle(Paint.Style.STROKE);
			mMarkPaint.setStrokeWidth(1.5f * c.getResources().getDisplayMetrics().density);
			mTextPaint.setColor(0xCCFFFFFF);
			mTextPaint.setTextAlign(Paint.Align.CENTER);
			mTextPaint.setTextSize(11 * c.getResources().getDisplayMetrics().density);
			setBackgroundColor(0x44000000);
		}
		
		void setListener(Listener l) {
			mListener = l;
		}
		
		private void recalc() {
			float w = getWidth(), h = getHeight();
			float lblH = mTextPaint.getTextSize() + dp(4);
			trkT = lblH;
			trkB = h - lblH;
			trkH = trkB - trkT;
			trkW = dp(16);
			mid = (trkT + trkB) / 2f;
			cx = w / 2f;
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			recalc();
			float h = getHeight();
			RectF track = new RectF(cx - trkW / 2f, trkT, cx + trkW / 2f, trkB);
			canvas.drawRoundRect(track, dp(5), dp(5), mTrackPaint);
			canvas.drawLine(cx - trkW / 2f - dp(6), mid, cx + trkW / 2f + dp(6), mid, mMarkPaint);
			float thumbCY = mid - mPos * trkH / 2f;
			float thumbH = dp(28), thumbW = trkW + dp(12);
			mThumbPaint.setAlpha((int) (160 + 90 * Math.abs(mPos)));
			canvas.drawRoundRect(
			new RectF(cx - thumbW / 2f, thumbCY - thumbH / 2f, cx + thumbW / 2f, thumbCY + thumbH / 2f), dp(6),
			dp(6), mThumbPaint);
			Paint.FontMetrics fm = mTextPaint.getFontMetrics();
			float pad = mTextPaint.getTextSize() + dp(2);
			canvas.drawText("T+", cx, pad / 2f - (fm.ascent + fm.descent) / 2f, mTextPaint);
			canvas.drawText("W−", cx, h - pad / 2f - fm.ascent, mTextPaint);
		}
		
		@Override
		public boolean onTouchEvent(MotionEvent e) {
			recalc();
			switch (e.getAction()) {
				case MotionEvent.ACTION_DOWN:
				case MotionEvent.ACTION_MOVE:
				removeCallbacks(mSpring);
				mTracking = true;
				mPos = Math.max(-1f, Math.min(1f, (mid - e.getY()) / (trkH / 2f)));
				if (mListener != null)
				mListener.onLever(mPos);
				invalidate();
				return true;
				case MotionEvent.ACTION_UP:
				case MotionEvent.ACTION_CANCEL:
				mTracking = false;
				post(mSpring);
				return true;
			}
			return super.onTouchEvent(e);
		}
		
		private final Runnable mSpring = new Runnable() {
			@Override
			public void run() {
				if (mTracking)
				return;
				mPos *= 0.75f;
				if (mListener != null)
				mListener.onLever(mPos);
				invalidate();
				if (Math.abs(mPos) > 0.01f)
				postDelayed(this, 16);
				else {
					mPos = 0f;
					if (mListener != null)
					mListener.onLever(0f);
					invalidate();
				}
			}
		};
		
		private int dp(int x) {
			return Math.round(x * getResources().getDisplayMetrics().density);
		}
	}
	
	// ─── Focus Assist — зумированное окно в центре экрана ───────────────────
	// Захватывает центральную область превью через PixelCopy и рисует её
	// с увеличением x4. Обновляется каждые ~100 мс.
	// Поверх — сетка Петцваля и рамка.
	
	class FocusAssistView extends View implements Runnable {
		private Bitmap mBmp;
		private final Paint mBmpPaint = new Paint(Paint.ANTI_ALIAS_FLAG | Paint.FILTER_BITMAP_FLAG);
		private final Paint mBorderPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mGridPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private static final int ZOOM = 4;
		private static final int SAMPLE_SIZE = 120; // px стороны захватываемого квадрата
		private volatile boolean mRunning;
		
		FocusAssistView(Context c) {
			super(c);
			mBorderPaint.setColor(0xFFDDCC00);
			mBorderPaint.setStyle(Paint.Style.STROKE);
			mBorderPaint.setStrokeWidth(2f);
			mGridPaint.setColor(0x55FFFFFF);
			mGridPaint.setStyle(Paint.Style.STROKE);
			mGridPaint.setStrokeWidth(0.8f);
			mLabelPaint.setColor(0xFFDDCC00);
			mLabelPaint.setTextAlign(Paint.Align.CENTER);
			mLabelPaint.setTextSize(10 * getResources().getDisplayMetrics().density);
			mLabelPaint.setAntiAlias(true);
			setBackgroundColor(0x00000000);
		}
		
		@Override
		protected void onAttachedToWindow() {
			super.onAttachedToWindow();
			mRunning = true;
			postDelayed(this, 100);
		}
		
		@Override
		protected void onDetachedFromWindow() {
			super.onDetachedFromWindow();
			mRunning = false;
			removeCallbacks(this);
		}
		
		@Override
		public void run() {
			if (!mRunning || getVisibility() != View.VISIBLE) {
				if (mRunning) postDelayed(this, 200);
				return;
			}
			capture();
			postDelayed(this, 100);
		}
		
		private void capture() {
			if (mSv == null || !mSurfaceReady) return;
			if (android.os.Build.VERSION.SDK_INT < 26) {
				// PixelCopy недоступен — рисуем заглушку
				invalidate();
				return;
			}
			try {
				int svW = mSv.getWidth(), svH = mSv.getHeight();
				if (svW <= 0 || svH <= 0) return;
				
				// Центральная область SAMPLE_SIZE × SAMPLE_SIZE
				int cx = svW / 2, cy = svH / 2, half = SAMPLE_SIZE / 2;
				int l = Math.max(0, cx - half), t = Math.max(0, cy - half);
				int r = Math.min(svW, l + SAMPLE_SIZE), b = Math.min(svH, t + SAMPLE_SIZE);
				android.graphics.Rect src = new android.graphics.Rect(l, t, r, b);
				
				Bitmap dst = Bitmap.createBitmap(r - l, b - t, Bitmap.Config.ARGB_8888);
				android.view.PixelCopy.request(mSv, src, dst, result -> {
					if (result == android.view.PixelCopy.SUCCESS) {
						mBmp = dst;
						postInvalidate();
					}
				}, new Handler(android.os.Looper.getMainLooper()));
			} catch (Exception ignored) {}
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			
			// Фон — чёрный полупрозрачный
			canvas.drawARGB(200, 0, 0, 0);
			
			if (mBmp != null && !mBmp.isRecycled()) {
				// Рисуем захваченный фрагмент, растянутый на весь квадрат
				android.graphics.RectF dst = new android.graphics.RectF(0, 0, w, h);
				canvas.drawBitmap(mBmp, null, dst, mBmpPaint);
				} else {
				// Заглушка когда PixelCopy ещё не отработал
				Paint p = new Paint();
				p.setColor(0xFF333333);
				canvas.drawRect(0, 0, w, h, p);
			}
			
			// Сетка — тонкая перекрёстная линия (центральная)
			canvas.drawLine(w / 2f, 0, w / 2f, h, mGridPaint);
			canvas.drawLine(0, h / 2f, w, h / 2f, mGridPaint);
			// Третьи (по правило третей)
			canvas.drawLine(w / 3f, 0, w / 3f, h, mGridPaint);
			canvas.drawLine(2 * w / 3f, 0, 2 * w / 3f, h, mGridPaint);
			canvas.drawLine(0, h / 3f, w, h / 3f, mGridPaint);
			canvas.drawLine(0, 2 * h / 3f, w, 2 * h / 3f, mGridPaint);
			
			// Рамка
			canvas.drawRect(1f, 1f, w - 1f, h - 1f, mBorderPaint);
			
			// Уголки (более жирные акценты)
			float corner = w * 0.12f;
			mBorderPaint.setStrokeWidth(3f);
			canvas.drawLine(1f, 1f, corner, 1f, mBorderPaint);
			canvas.drawLine(1f, 1f, 1f, corner, mBorderPaint);
			canvas.drawLine(w - corner, 1f, w - 1f, 1f, mBorderPaint);
			canvas.drawLine(w - 1f, 1f, w - 1f, corner, mBorderPaint);
			canvas.drawLine(1f, h - corner, 1f, h - 1f, mBorderPaint);
			canvas.drawLine(1f, h - 1f, corner, h - 1f, mBorderPaint);
			canvas.drawLine(w - 1f, h - corner, w - 1f, h - 1f, mBorderPaint);
			canvas.drawLine(w - corner, h - 1f, w - 1f, h - 1f, mBorderPaint);
			mBorderPaint.setStrokeWidth(2f);
			
			// Подпись
			canvas.drawText("FOCUS ×" + ZOOM, w / 2f, h - 4f, mLabelPaint);
		}
	}
	
	// ─── Барабан фокуса (как кольцо на настоящей камере) ────────────────────
	// Свайп вниз = фокус вдаль (∞), свайп вверх = макро.
	// Визуально: риски на цилиндре с перспективным сжатием.
	
	static class FocusDrumView extends View {
		interface OnFocusChangeListener {
			void onFocusChanged(float value); // 0=∞, 1=macro
		}
		
		/** Коллбэк начала/остановки прокрутки барабана */
		interface OnDrumScrollListener {
			void onScrollStart();
			void onScrollStop();
		}
		
		private OnFocusChangeListener mListener;
		private OnDrumScrollListener mScrollListener;
		private float mValue = 0f; // 0..1
		private float mLastY;
		private boolean mDragging;
		
		// Визуальный «угол» барабана — непрерывный для анимации рисок
		private float mAngle = 0f;
		private static final float FULL_RANGE_PX_PER_UNIT = 800f;
		
		private final Paint mDrumPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mRiskPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mShadowPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mCenterLinePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		
		FocusDrumView(Context c) {
			super(c);
			float density = c.getResources().getDisplayMetrics().density;
			mDrumPaint.setColor(0xFF2A2A2A);
			mRiskPaint.setStrokeWidth(1.5f * density);
			mRiskPaint.setStyle(Paint.Style.STROKE);
			mShadowPaint.setStyle(Paint.Style.FILL);
			mCenterLinePaint.setColor(0xFFDDCC00);
			mCenterLinePaint.setStrokeWidth(2f * density);
			mCenterLinePaint.setStyle(Paint.Style.STROKE);
		}
		
		void setOnFocusChangeListener(OnFocusChangeListener l) {
			mListener = l;
		}
		
		void setOnDrumScrollListener(OnDrumScrollListener l) {
			mScrollListener = l;
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			final float cx = w / 2f;
			final float drumW = w * 0.72f;
			final float drumLeft = cx - drumW / 2f;
			final float drumRight = cx + drumW / 2f;
			
			// Фон барабана
			RectF drumRect = new RectF(drumLeft, 0, drumRight, h);
			mDrumPaint.setColor(0xFF222222);
			canvas.drawRoundRect(drumRect, drumW * 0.12f, drumW * 0.12f, mDrumPaint);
			
			// Риски барабана с перспективным сжатием
			final float riskStep = h * 0.07f;
			float offset = mAngle % riskStep;
			if (offset < 0) offset += riskStep;
			
			final int totalRisks = (int) (h / riskStep) + 2;
			for (int i = -1; i <= totalRisks; i++) {
				float ry = offset + i * riskStep;
				if (ry < 0 || ry > h) continue;
				
				float distFromCenter = Math.abs(ry - h / 2f) / (h / 2f);
				float squeeze = 1f - 0.55f * distFromCenter * distFromCenter;
				float riskLen = drumW * 0.8f * squeeze;
				int alpha = (int) (200 * (1f - distFromCenter * 0.7f));
				
				boolean isMajor = (Math.abs(Math.round((ry - offset) / riskStep)) % 5 == 0);
				if (isMajor) { riskLen *= 1.25f; alpha = Math.min(255, alpha + 40); }
				
				mRiskPaint.setColor(0xFFFFFFFF);
				mRiskPaint.setAlpha(alpha);
				mRiskPaint.setStrokeWidth(isMajor ? 2f : 1.2f);
				canvas.drawLine(cx - riskLen / 2f, ry, cx + riskLen / 2f, ry, mRiskPaint);
			}
			
			// Градиентные тени сверху/снизу (имитация цилиндра)
			int[] colorsTop = { 0xCC000000, 0x00000000 };
			int[] colorsBot = { 0x00000000, 0xCC000000 };
			android.graphics.LinearGradient shadTop = new android.graphics.LinearGradient(
			0, 0, 0, h * 0.28f, colorsTop, null, android.graphics.Shader.TileMode.CLAMP);
			android.graphics.LinearGradient shadBot = new android.graphics.LinearGradient(
			0, h * 0.72f, 0, h, colorsBot, null, android.graphics.Shader.TileMode.CLAMP);
			mShadowPaint.setShader(shadTop);
			canvas.drawRoundRect(drumRect, drumW * 0.12f, drumW * 0.12f, mShadowPaint);
			mShadowPaint.setShader(shadBot);
			canvas.drawRoundRect(drumRect, drumW * 0.12f, drumW * 0.12f, mShadowPaint);
			mShadowPaint.setShader(null);
			
			// Центральная риска-указатель (жёлтая)
			canvas.drawLine(drumLeft - 4f, h / 2f, drumRight + 4f, h / 2f, mCenterLinePaint);
		}
		
		@Override
		public boolean onTouchEvent(MotionEvent e) {
			switch (e.getAction()) {
				case MotionEvent.ACTION_DOWN:
				mLastY = e.getY();
				mDragging = true;
				if (mScrollListener != null) mScrollListener.onScrollStart();
				return true;
				case MotionEvent.ACTION_MOVE: {
					if (!mDragging) return true;
					float dy = e.getY() - mLastY;
					mLastY = e.getY();
					// Свайп вниз → фокус на ∞ (value уменьшается)
					// Свайп вверх → макро (value увеличивается)
					mAngle += dy;
					float newVal = mValue - dy / FULL_RANGE_PX_PER_UNIT;
					newVal = Math.max(0f, Math.min(1f, newVal));
					// Фиксируем барабан у упора
					if (newVal == 0f && mValue == 0f) mAngle = Math.min(mAngle, 0f);
					if (newVal == 1f && mValue == 1f) mAngle = Math.max(mAngle, 0f);
					if (newVal != mValue) {
						mValue = newVal;
						if (mListener != null) mListener.onFocusChanged(mValue);
					}
					invalidate();
					return true;
				}
				case MotionEvent.ACTION_UP:
				case MotionEvent.ACTION_CANCEL:
				mDragging = false;
				if (mScrollListener != null) mScrollListener.onScrollStop();
				return true;
			}
			return false;
		}
	}

	// ─── Осциллограф с триггером ─────────────────────────────────────────────
	// Прозрачный фон, наложен поверх изображения камеры.
	// Триггер: фронт нарастания (rising edge) при пересечении порога.
	// Окно отображения — 2048 выборок (~46 мс при 44100 Гц).
	
	static class OscilloscopeView extends View {
		private static final int DISP_SAMPLES = 2048;
		private static final int BUF_SIZE = DISP_SAMPLES * 4; // кольцевой буфер
		
		private final float[] mRingBuf = new float[BUF_SIZE];
		private int mWritePos = 0;
		private final float[] mFrame = new float[DISP_SAMPLES];
		private volatile boolean mNewFrame = false;
		private final Object mLock = new Object();
		
		// Триггер
		private static final float TRIG_LEVEL = 0.05f; // нормализованный уровень
		private static final int TRIG_HYSTERESIS = 64; // выборок предыстории
		
		private final Paint mWavePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mGridPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		/** Цвет по амплитуде 0..1 — как сегменты VU-метра */
		static int levelColor(float amp) {
			if (amp >= 0.7f) return 0xFFFF2200;
			if (amp >= 0.3f) return 0xFFFFBB00;
			return 0xFF00CC55;
		}

		OscilloscopeView(Context c) {
			super(c);
			setBackgroundColor(0x00000000); // прозрачный
			mWavePaint.setStrokeWidth(1.8f * c.getResources().getDisplayMetrics().density);
			mWavePaint.setStyle(Paint.Style.STROKE);
			mWavePaint.setStrokeCap(Paint.Cap.ROUND);
			mGridPaint.setColor(0x33FFFFFF);
			mGridPaint.setStrokeWidth(0.8f);
			mGridPaint.setStyle(Paint.Style.STROKE);
			mLabelPaint.setColor(0xAAFFFFFF);
			mLabelPaint.setTextSize(9 * c.getResources().getDisplayMetrics().density);
			mLabelPaint.setAntiAlias(true);
		}
		
		/** Принимает буфер PCM-16, конвертирует в mono float и кладёт в кольцевой буфер */
		void pushSamples(short[] buf, int len, int channels) {
			synchronized (mLock) {
				for (int i = 0; i < len; i += channels) {
					float mono = buf[i] / 32768f;
					if (channels == 2 && i + 1 < len)
						mono = (mono + buf[i + 1] / 32768f) * 0.5f;
					mRingBuf[mWritePos] = mono;
					mWritePos = (mWritePos + 1) % BUF_SIZE;
				}
				// Поиск триггера: восходящий фронт >= TRIG_LEVEL
				// Ищем в последних BUF_SIZE выборках
				int trigPos = -1;
				int searchStart = (mWritePos - BUF_SIZE + BUF_SIZE) % BUF_SIZE;
				for (int k = TRIG_HYSTERESIS; k < BUF_SIZE - DISP_SAMPLES; k++) {
					int p = (searchStart + k) % BUF_SIZE;
					int pp = (p - 1 + BUF_SIZE) % BUF_SIZE;
					if (mRingBuf[pp] < TRIG_LEVEL && mRingBuf[p] >= TRIG_LEVEL) {
						trigPos = p;
						break;
					}
				}
				if (trigPos < 0) {
					// Триггер не найден — показываем последние DISP_SAMPLES
					trigPos = (mWritePos - DISP_SAMPLES + BUF_SIZE) % BUF_SIZE;
				}
				for (int k = 0; k < DISP_SAMPLES; k++) {
					mFrame[k] = mRingBuf[(trigPos + k) % BUF_SIZE];
				}
				mNewFrame = true;
			}
			postInvalidate();
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			if (w == 0 || h == 0) return;

			// Полностью прозрачный фон — не рисуем ничего
			// canvas.drawARGB(90, 0, 0, 0);
			
			// Сетка
			for (int gx = 1; gx < 4; gx++)
				canvas.drawLine(w * gx / 4f, 0, w * gx / 4f, h, mGridPaint);
			for (int gy = 1; gy < 4; gy++)
				canvas.drawLine(0, h * gy / 4f, w, h * gy / 4f, mGridPaint);
			// Ось Y = 0
			Paint zeroPaint = new Paint(mGridPaint);
			zeroPaint.setColor(0x55FFFFFF);
			zeroPaint.setStrokeWidth(1.4f);
			canvas.drawLine(0, h / 2f, w, h / 2f, zeroPaint);
			
			// Линия уровня триггера
			Paint trigPaint = new Paint();
			trigPaint.setColor(0x88FFFF00);
			trigPaint.setStrokeWidth(1f);
			trigPaint.setStyle(Paint.Style.STROKE);
			trigPaint.setPathEffect(new android.graphics.DashPathEffect(new float[]{6f, 4f}, 0));
			float trigY = h / 2f - TRIG_LEVEL * h / 2f;
			canvas.drawLine(0, trigY, w, trigY, trigPaint);
			
			// Волна — цветные сегменты (зелёный→оранжевый→красный)
			float[] frame;
			synchronized (mLock) {
				frame = mFrame.clone();
			}
			for (int i = 0; i < DISP_SAMPLES - 1; i++) {
				float x0 = i       * w / (DISP_SAMPLES - 1f);
				float x1 = (i + 1) * w / (DISP_SAMPLES - 1f);
				float y0 = h / 2f - frame[i]     * h / 2f * 0.92f;
				float y1 = h / 2f - frame[i + 1] * h / 2f * 0.92f;
				mWavePaint.setColor(levelColor(Math.abs(frame[i])));
				canvas.drawLine(x0, y0, x1, y1, mWavePaint);
			}
			
			// Подпись
			canvas.drawText("OSC  T↑", 4, h - 3f, mLabelPaint);
		}
	}
	

	// ─── Огибающая: бегущий 10-секундный осциллограф ────────────────────────────
	// Хранит пиковые значения с шагом ~10 мс (CHUNK выборок).
	// Показывается когда осциллограф выключен; вертикальный масштаб совпадает.

	static class EnvelopeView extends View {
		private static final int HIST  = 1000; // 10 с × 100 точек/с
		private static final int CHUNK = 441;  // ~10 мс при 44100 Гц

		private final float[] mEnv    = new float[HIST];
		private int   mWritePos = 0;
		private int   mFilled   = 0;
		private float mAccPeak  = 0f;
		private int   mAccCount = 0;
		private final Object mLock = new Object();

		private final Paint mSegPaint   = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mGridPaint  = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);

		EnvelopeView(Context c) {
			super(c);
			setBackgroundColor(0x00000000);
			float d = c.getResources().getDisplayMetrics().density;
			mSegPaint.setStyle(Paint.Style.STROKE);
			mSegPaint.setStrokeWidth(1.6f * d);
			mSegPaint.setStrokeCap(Paint.Cap.ROUND);
			mGridPaint.setColor(0x33FFFFFF);
			mGridPaint.setStrokeWidth(0.8f);
			mGridPaint.setStyle(Paint.Style.STROKE);
			mLabelPaint.setColor(0xAAFFFFFF);
			mLabelPaint.setTextSize(9 * d);
			mLabelPaint.setAntiAlias(true);
		}

		void pushSamples(short[] buf, int len, int channels) {
			synchronized (mLock) {
				for (int i = 0; i < len; i += channels) {
					float s = Math.abs(buf[i] / 32768f);
					if (channels == 2 && i + 1 < len)
						s = Math.max(s, Math.abs(buf[i + 1] / 32768f));
					if (s > mAccPeak) mAccPeak = s;
					mAccCount++;
					if (mAccCount >= CHUNK) {
						mEnv[mWritePos] = mAccPeak;
						mWritePos = (mWritePos + 1) % HIST;
						if (mFilled < HIST) mFilled++;
						mAccPeak  = 0f;
						mAccCount = 0;
					}
				}
			}
			postInvalidate();
		}

		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			if (w == 0 || h == 0) return;

			// Сетка (как у осциллографа)
			for (int gx = 1; gx < 4; gx++)
				canvas.drawLine(w * gx / 4f, 0, w * gx / 4f, h, mGridPaint);
			for (int gy = 1; gy < 4; gy++)
				canvas.drawLine(0, h * gy / 4f, w, h * gy / 4f, mGridPaint);
			Paint zeroPaint = new Paint(mGridPaint);
			zeroPaint.setColor(0x55FFFFFF);
			zeroPaint.setStrokeWidth(1.4f);
			canvas.drawLine(0, h / 2f, w, h / 2f, zeroPaint);

			float[] snap;
			int filled, writePos;
			synchronized (mLock) {
				snap     = mEnv.clone();
				filled   = mFilled;
				writePos = mWritePos;
			}
			if (filled < 2) {
				mLabelPaint.setColor(0xAAFFFFFF);
				canvas.drawText("ENV  10s", 4, h - 3f, mLabelPaint);
				return;
			}

			int count = Math.min(filled, HIST);
			int start = (filled < HIST) ? 0 : writePos;

			// Рисуем симметричную огибающую цветными сегментами
			for (int i = 0; i < count - 1; i++) {
				float a0 = snap[(start + i)     % HIST];
				float a1 = snap[(start + i + 1) % HIST];
				float x0 = i       * w / (count - 1f);
				float x1 = (i + 1) * w / (count - 1f);
				float yT0 = h / 2f - a0 * h / 2f * 0.92f;
				float yT1 = h / 2f - a1 * h / 2f * 0.92f;
				float yB0 = h / 2f + a0 * h / 2f * 0.92f;
				float yB1 = h / 2f + a1 * h / 2f * 0.92f;
				mSegPaint.setColor(OscilloscopeView.levelColor((a0 + a1) * 0.5f));
				canvas.drawLine(x0, yT0, x1, yT1, mSegPaint);
				canvas.drawLine(x0, yB0, x1, yB1, mSegPaint);
			}

			// Вертикальная черта «сейчас» (правый край)
			Paint curPaint = new Paint();
			curPaint.setColor(0x66FFFFFF);
			curPaint.setStrokeWidth(1f);
			canvas.drawLine(w - 1f, 0, w - 1f, h, curPaint);

			mLabelPaint.setColor(0xAAFFFFFF);
			canvas.drawText("ENV  10s", 4, h - 3f, mLabelPaint);
		}
	}

	// ─── Спектр-анализатор: FFT 2048 точек ───────────────────────────────────
	// Компактный вид в нижней панели. Логарифмическая шкала частот.
	// Накопительный буфер: когда накоплено >= FFT_SIZE выборок — считаем FFT.
	
	static class SpectrumView extends View {
		private static final int FFT_SIZE = 2048;
		private static final int HALF = FFT_SIZE / 2;
		
		private final float[] mAccBuf = new float[FFT_SIZE];
		private int mAccPos = 0;
		
		private final float[] mMagnitude = new float[HALF]; // последний спектр
		private final float[] mSmooth = new float[HALF];    // сглаженный
		private final float[] mPeaks = new float[HALF];     // пик-холд для спектра
		private final Object mLock = new Object();
		
		// FFT рабочие массивы (переиспользуются)
		private final float[] mFftRe = new float[FFT_SIZE];
		private final float[] mFftIm = new float[FFT_SIZE];
		// Окно Ханна
		private final float[] mWindow = new float[FFT_SIZE];
		
		private final Paint mBarPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mPeakPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLblPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mBgPaint = new Paint();
		
		private static final int DISPLAY_BINS = 60; // уменьшено вдвое
		private static final float SAMPLE_RATE = 44100f;
		private static final float DECAY = 0.82f;    // коэффициент спада сглаженного
		private static final float PEAK_DECAY = 0.996f;
		
		SpectrumView(Context c) {
			super(c);
			// Окно Ханна
			for (int i = 0; i < FFT_SIZE; i++)
				mWindow[i] = 0.5f * (1f - (float) Math.cos(2.0 * Math.PI * i / (FFT_SIZE - 1)));
			mBarPaint.setStyle(Paint.Style.FILL);
			mPeakPaint.setStyle(Paint.Style.STROKE);
			mPeakPaint.setColor(0xFFFFFFFF);
			mPeakPaint.setStrokeWidth(1.5f);
			mLblPaint.setColor(0xCCFFFFFF);
			mLblPaint.setTextSize(7.5f * c.getResources().getDisplayMetrics().density);
			mLblPaint.setAntiAlias(true);
			mBgPaint.setColor(0x00000000); // полностью прозрачный фон
		}
		
		/** Получает новый блок PCM-16, микширует в моно, накапливает до FFT_SIZE */
		void pushSamples(short[] buf, int len, int channels) {
			for (int i = 0; i < len; i += channels) {
				float mono = buf[i] / 32768f;
				if (channels == 2 && i + 1 < len)
					mono = (mono + buf[i + 1] / 32768f) * 0.5f;
				mAccBuf[mAccPos++] = mono;
				if (mAccPos >= FFT_SIZE) {
					computeFFT();
					// Перекрытие 50% — сдвигаем буфер
					System.arraycopy(mAccBuf, FFT_SIZE / 2, mAccBuf, 0, FFT_SIZE / 2);
					mAccPos = FFT_SIZE / 2;
				}
			}
		}
		
		private void computeFFT() {
			// Применяем окно Ханна
			for (int i = 0; i < FFT_SIZE; i++) {
				mFftRe[i] = mAccBuf[i] * mWindow[i];
				mFftIm[i] = 0f;
			}
			// Cooley-Tukey in-place radix-2 DIT FFT
			int n = FFT_SIZE;
			for (int i = 1, j = 0; i < n; i++) {
				int bit = n >> 1;
				for (; (j & bit) != 0; bit >>= 1) j ^= bit;
				j ^= bit;
				if (i < j) {
					float tr = mFftRe[i]; mFftRe[i] = mFftRe[j]; mFftRe[j] = tr;
					float ti = mFftIm[i]; mFftIm[i] = mFftIm[j]; mFftIm[j] = ti;
				}
			}
			for (int len = 2; len <= n; len <<= 1) {
				double ang = -2.0 * Math.PI / len;
				float wRe = (float) Math.cos(ang), wIm = (float) Math.sin(ang);
				for (int i = 0; i < n; i += len) {
					float curRe = 1f, curIm = 0f;
					for (int k = 0; k < len / 2; k++) {
						float uRe = mFftRe[i + k], uIm = mFftIm[i + k];
						float vRe = mFftRe[i + k + len/2] * curRe - mFftIm[i + k + len/2] * curIm;
						float vIm = mFftRe[i + k + len/2] * curIm + mFftIm[i + k + len/2] * curRe;
						mFftRe[i + k]         = uRe + vRe;
						mFftIm[i + k]         = uIm + vIm;
						mFftRe[i + k + len/2] = uRe - vRe;
						mFftIm[i + k + len/2] = uIm - vIm;
						float nRe = curRe * wRe - curIm * wIm;
						curIm = curRe * wIm + curIm * wRe;
						curRe = nRe;
					}
				}
			}
			// Вычисляем амплитуду в дБ
			synchronized (mLock) {
				for (int i = 0; i < HALF; i++) {
					float mag = (float) Math.sqrt(mFftRe[i]*mFftRe[i] + mFftIm[i]*mFftIm[i]) / (FFT_SIZE / 2f);
					float db = mag > 1e-9f ? Math.max(-90f, (float)(20.0 * Math.log10(mag))) : -90f;
					// Нормализуем 0..1 (от -90dB до 0dB)
					float norm = (db + 90f) / 90f;
					mMagnitude[i] = norm;
					mSmooth[i] = Math.max(norm, mSmooth[i] * DECAY);
					mPeaks[i] = Math.max(mSmooth[i], mPeaks[i] * PEAK_DECAY);
				}
			}
			postInvalidate();
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			if (w == 0 || h == 0) return;

			// Фон полностью прозрачный — не рисуем ничего
			// canvas.drawRect(0, 0, w, h, mBgPaint);

			final float lblH = mLblPaint.getTextSize() + 4f;
			final float barTop   = lblH;            // верхняя полоса зарезервирована под метки
			final float barAreaH = h - barTop;      // высота зоны баров

			float[] freqMarks  = {50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000};
			String[] freqLabels = {"50", "100", "200", "500", "1k", "2k", "5k", "10k", "20k"};
			float fMin = (float) Math.log10(20.0);
			float fMax = (float) Math.log10(SAMPLE_RATE / 2f);

			// Сетка только в зоне баров (ниже полосы меток)
			Paint gridPaint = new Paint();
			gridPaint.setColor(0x44FFFFFF);
			gridPaint.setStrokeWidth(0.8f);
			for (int fi = 0; fi < freqMarks.length; fi++) {
				if (freqMarks[fi] > SAMPLE_RATE / 2f) break;
				float xf = ((float) Math.log10(freqMarks[fi]) - fMin) / (fMax - fMin) * w;
				canvas.drawLine(xf, barTop, xf, h, gridPaint);
			}

			// Полосы спектра
			float[] smooth, peaks;
			synchronized (mLock) {
				smooth = mSmooth.clone();
				peaks  = mPeaks.clone();
			}

			float logFMin  = (float) Math.log10(Math.max(1f, 20f));
			float logFMaxV = (float) Math.log10(SAMPLE_RATE / 2f);

			for (int b = 0; b < DISPLAY_BINS; b++) {
				float logF0 = logFMin + (float) b       / DISPLAY_BINS * (logFMaxV - logFMin);
				float logF1 = logFMin + (float)(b + 1)  / DISPLAY_BINS * (logFMaxV - logFMin);
				float f0 = (float) Math.pow(10.0, logF0);
				float f1 = (float) Math.pow(10.0, logF1);

				int bin0 = Math.max(0,        Math.round(f0 / SAMPLE_RATE * FFT_SIZE));
				int bin1 = Math.min(HALF - 1, Math.round(f1 / SAMPLE_RATE * FFT_SIZE));

				float val = 0f, pk = 0f;
				for (int i = bin0; i <= bin1; i++) {
					if (smooth[i] > val) val = smooth[i];
					if (peaks[i]  > pk)  pk  = peaks[i];
				}

				float x0 = (float) b       / DISPLAY_BINS * w;
				float x1 = (float)(b + 1)  / DISPLAY_BINS * w - 1f;
				if (x1 < x0 + 0.5f) x1 = x0 + 0.5f;

				int red   = Math.min(255, (int)(val * 510f));
				int green = Math.min(255, (int)((1f - val) * 510f));
				mBarPaint.setColor(0xDD000000 | (red << 16) | (green << 8) | 0x22);
				float barH = val * barAreaH;
				canvas.drawRect(x0, h - barH, x1, h, mBarPaint);

				if (pk > 0.02f) {
					float peakY = h - pk * barAreaH;
					canvas.drawLine(x0, peakY, x1, peakY, mPeakPaint);
				}
			}

			// ── Метки частот в верхней полосе (всегда видны) ───────────────
			float labelY = lblH - 4f;
			float prevLblRight = -1f;
			mLblPaint.setTextAlign(Paint.Align.CENTER);
			for (int fi = 0; fi < freqMarks.length; fi++) {
				if (freqMarks[fi] > SAMPLE_RATE / 2f) break;
				float xf = ((float) Math.log10(freqMarks[fi]) - fMin) / (fMax - fMin) * w;
				float lblW = mLblPaint.measureText(freqLabels[fi]);
				float lblX = xf - lblW / 2f;
				if (lblX > prevLblRight && lblX + lblW < w - 2f) {
					canvas.drawText(freqLabels[fi], xf, labelY, mLblPaint);
					prevLblRight = lblX + lblW + 3f;
				}
			}
		}
	}

}
