#include "../Zend/zend_compile.h"
#include "zend.h"
#include "zend_modules.h"
#include <unistd.h>
#include <string.h> /* For the real memset prototype.  */
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <sys/types.h>
#include <sys/shm.h>
#include <sys/wait.h>

#include <time.h>

#include <pthread.h>
#include <unistd.h>

int value_diff_changes(char *var1, char *var2);
void value_diff_report(char *var1, char *var2, int bitmapLoc);
void var_diff_report(char *var1, int bitmapLoc, int var_type);
void dbg_printf(const char *fmt, ...);

#ifdef WITCHER_DEBUG
#define debug_print(xval) \
    do                    \
    {                     \
        dbg_printf xval;  \
    } while (0)
#else
#define debug_print(fmt, ...)
#endif

/***** END new for HTTP direct ********/

#define MAPSIZE 65536
#define TRACE_SIZE 128 * (1024 * 1024) // X * megabytes

#define SHM_ENV_VAR "__AFL_SHM_ID"

#define STDIN_FILENO 0

static int last = 0;
static int op = 0;

static int MAX_CMDLINE_LEN = 128 * 1024;

static unsigned char *afl_area_ptr = NULL;

unsigned int afl_forksrv_pid = 0;
static unsigned char afl_fork_child;

#define FORKSRV_FD 198
#define TSL_FD (FORKSRV_FD - 1)

#define MAX_VARIABLES 1024
char *variables[3][MAX_VARIABLES];
unsigned char variables_used[3][MAX_VARIABLES];
int variables_ptr[3] = {0, 0, 0};

char *traceout_fn, *traceout_path;

int nextVar2_is_a_var = -1;
bool wc_extra_instr = true;

static bool start_tracing = false;

static char *env_vars[2] = {"HTTP_COOKIE", "QUERY_STRING"};
char *login_cookie = NULL, *mandatory_cookie = NULL, *preset_cookie = NULL;
char *witcher_print_op = NULL;

char *main_filename;
char session_id[40];
int saved_session_size = 0;

int trace[TRACE_SIZE];
int trace_index = 0;

int pipefds[2];

int top_pid = 0;

void dbg_printf(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    vfprintf(stderr, fmt, args);
    va_end(args);
}

/**
 * Mostly taken from the afl_forkserver code provided with AFL
 * Injects a fork server into php_cgi to speed things up
 */
static void afl_forkserver()
{
    printf("afl_forkserver()\n");

    static unsigned char tmp[4];

    if (!afl_area_ptr)
        return;
    if (write(FORKSRV_FD + 1, tmp, 4) != 4)
        return;

    afl_forksrv_pid = getpid();

    /* All right, let's await orders... */
    int claunch_cnt = 0;
    while (1)
    {

        pid_t child_pid = -1;
        int status, t_fd[2];

        /* Whoops, parent dead? */
        if (read(FORKSRV_FD, tmp, 4) != 4)
            exit(2);

        /* Establish a channel with child to grab translation commands. We'll
           read from t_fd[0], child will write to TSL_FD. */
        if (pipe(t_fd) || dup2(t_fd[1], TSL_FD) < 0)
            exit(3);
        close(t_fd[1]);
        claunch_cnt++;
        child_pid = fork();

        fflush(stdout);
        if (child_pid < 0)
            exit(4);

        if (!child_pid)
        { // child_pid == 0, i.e., in child

            FILE *fptr;
            fptr = fopen("/tmp/httpreqr.pid", "w");
            if (fptr)
            {
                fprintf(fptr, "%d", getpid());
                fclose(fptr);
            }

            /* Child process. Close descriptors and run free. */
            debug_print(("\t\t\tlaunch cnt = %d Child pid == %d, but current pid = %d\n", claunch_cnt, child_pid, getpid()));
            fflush(stdout);
            afl_fork_child = 1;
            close(FORKSRV_FD);
            close(FORKSRV_FD + 1);
            close(t_fd[0]);
            return;
        }

        /* Parent. */

        close(TSL_FD);

        if (write(FORKSRV_FD + 1, &child_pid, 4) != 4)
        {
            debug_print(("\t\tExiting Parent %d with 5\n", child_pid));
            exit(5);
        }

        /* Get and relay exit status to parent. */
        int waitedpid = waitpid(child_pid, &status, 0);
        if (waitedpid < 0)
        {
            printf("\t\tExiting Parent %d with 6\n", child_pid);
            exit(6);
        }

        if (write(FORKSRV_FD + 1, &status, 4) != 4)
        {
            exit(7);
        }
    }
}

void load_variables(char *str, int var_type)
{
    printf("load_variables()\n");
    char *tostr = strdup(str);
    char *end_str;
    char *token = strtok_r(tostr, "&", &end_str);

    while (token != NULL)
    {
        char *end_token;
        char *dup_token = strdup(token);
        char *subtok = strtok_r(dup_token, "=", &end_token);

        if (subtok != NULL && variables_ptr[var_type] < MAX_VARIABLES)
        {
            char *first_part = strdup(subtok);
            subtok = strtok_r(NULL, "=", &end_token);
            int len = strlen(first_part);
            if (len > 2)
            {
                bool unique = true;
                for (int i = 0; i < variables_ptr[var_type]; i++)
                {
                    if (strcmp(first_part, variables[var_type][i]) == 0)
                    {
                        unique = false;
                        break;
                    }
                }
                if (unique)
                {
                    int cur_ptr = variables_ptr[var_type];
                    variables[var_type][cur_ptr] = (char *)malloc(len + 1);
                    strncpy(variables[var_type][cur_ptr], first_part, len);
                    variables[var_type][cur_ptr][len] = '\x00';
                    variables_used[var_type][cur_ptr] = 0;
                    variables_ptr[var_type]++;
                }
            }
            token = strtok_r(NULL, "&", &end_str);
        }
        else
        {
            break;
        }
    }
}

char *replace_char(char *str, char find, char replace)
{
    printf("replace_char()\n");
    char *current_pos = strchr(str, find);
    while (current_pos)
    {
        *current_pos = replace;
        current_pos = strchr(current_pos, find);
    }
    return str;
}

char *format_to_json(char *str)
{
    printf("format_to_json()\n");

    char *tostr = strdup(str);
    char *outstr;
    outstr = (char *)malloc(strlen(str) + 1024);
    char *end_str;
    char *token = strtok_r(tostr, "&", &end_str);
    outstr = strcat(outstr, "{");

    while (token != NULL)
    {
        char jsonEleOut[strlen(str) + 7];
        char *end_token;
        char *dup_token = strdup(token);
        char *first_part = strtok_r(dup_token, "=", &end_token);
        char *sec_part = strtok_r(NULL, "=", &end_token);
        if (sec_part)
        {
            sprintf(jsonEleOut, "\"%s\":\"%s\",", first_part, sec_part);
        }
        else
        {
            sprintf(jsonEleOut, "\"%s\":\"\",", first_part);
        }
        outstr = strcat(outstr, jsonEleOut);
        token = strtok_r(NULL, "&", &end_str);
    }

    outstr[strlen(outstr) - 1] = '}';
    outstr[strlen(outstr)] = '\x00';

    return outstr;
}

/**
 * sets up the cgi environment for a cgi request
 */
void prefork_cgi_setup()
{
    printf("prefork_cgi_setup()\n");
    debug_print(("[\e[32mWitcher\e[0m] Starting SETUP_CGI_ENV  \n"));
    char *tmp = getenv("DOCUMENT_ROOT");
    if (!tmp)
    {
        setenv("DOCUMENT_ROOT", "/app", 1); // might be important if your cgi read/writes there
    }
    setenv("HTTP_REDIRECT_STATUS", "1", 1);

    setenv("HTTP_ACCEPT", "*/*", 1);
    setenv("GATEWAY_INTERFACE", "CGI/1.1", 1);

    setenv("PATH", "/usr/bin:/tmp:/app", 1); // HTTP URL PATH
    tmp = getenv("REQUEST_METHOD");
    if (!tmp)
    {
        setenv("REQUEST_METHOD", "POST", 1); // Usually GET or POST
    }
    setenv("REMOTE_ADDR", "127.0.0.1", 1);

    setenv("CONTENT_TYPE", "application/x-www-form-urlencoded", 1);
    setenv("REQUEST_URI", "SCRIPT", 1);
    login_cookie = getenv("LOGIN_COOKIE");

    // Save cookie value in /tmp/cookie.txt
    FILE *file = fopen("/tmp/cookie.txt", "w");

    if (file == NULL)
    {
        fprintf(stderr, "Failed to open the file.\n");
    }
    else
    {
        fprintf(file, "%s\n", login_cookie);

        fclose(file);
    }

    char *preset_cookie = (char *)malloc(MAX_CMDLINE_LEN);
    memset(preset_cookie, 0, MAX_CMDLINE_LEN);

    if (login_cookie)
    {
        strcat(preset_cookie, login_cookie);
        setenv(env_vars[0], login_cookie, 1);

        if (!strchr(login_cookie, ';'))
        {
            strcat(login_cookie, ";");
        }
        debug_print(("[\e[32mWitcher\e[0m] LOGIN COOKIE %s\n", login_cookie));
        char *name = strtok(login_cookie, ";=");
        while (name != NULL)
        {
            char *value = strtok(NULL, ";=");
            if (value != NULL)
            {
                debug_print(("\t%s==>%s\n", name, value)); // printing each token
            }
            else
            {
                debug_print(("\t%s==> NADA \n", name)); // printing each token
            }

            if (value != NULL)
            {
                int thelen = strlen(value);
                if (thelen >= 24 && thelen <= 32)
                {
                    debug_print(("[\e[32mWitcher\e[0m] session_id = %s, len=%d\n", value, thelen));
                    strcpy(session_id, value);
                    char filename[64];
                    char sess_fn[64];
                    sprintf(sess_fn, "../../../../../../../tmp/sess_%s", value);
                    setenv("SESSION_FILENAME", sess_fn, 1);

                    sprintf(filename, "../../../../../../../tmp/save_%s", value);

                    // saved_session_size = fsize(filename);

                    debug_print(("\t[WC] SESSION ID = %s, saved session size = %d\n", filename, saved_session_size));
                    break;
                }
            }
            name = strtok(NULL, ";=");
        }
        debug_print(("[\e[32mWitcher\e[0m] LOGIN ::> %s\n", login_cookie));
    }
    mandatory_cookie = getenv("MANDATORY_COOKIE");
    if (mandatory_cookie && strlen(mandatory_cookie) > 0)
    {
        strcat(preset_cookie, "; ");
        strcat(preset_cookie, mandatory_cookie);
        debug_print(("[\e[32mWitcher\e[0m] MANDATORY COOKIE = %s\n", preset_cookie));
    }
    witcher_print_op = getenv("WITCHER_PRINT_OP");
}
void setup_cgi_env()
{

    printf("setup_cgi_env()\n");

    // strict is set for the modified /bin/dash
#ifdef WITCHER_DEBUG
    FILE *logfile = fopen("/tmp/wrapper.log", "a+");
    fprintf(logfile, "----Start----\n");
    // printf("starting\n");
#endif

    static int num_env_vars = sizeof(env_vars) / sizeof(char *);

    char in_buf[MAX_CMDLINE_LEN];
    memset(in_buf, 0, MAX_CMDLINE_LEN);
    size_t bytes_read = read(0, in_buf, MAX_CMDLINE_LEN - 2);

    int zerocnt = 0;
    for (int cnt = 0; cnt < MAX_CMDLINE_LEN; cnt++)
    {
        if (in_buf[cnt] == 0)
        {
            zerocnt++;
        }
        if (zerocnt == 3)
        {
            break;
        }
    }

    pipe(pipefds);

    dup2(pipefds[0], STDIN_FILENO);
    // close(STDIN_FILENO);

    int real_content_length = 0;
    char *saved_ptr = (char *)malloc(MAX_CMDLINE_LEN);
    char *ptr = in_buf;
    int rc = 0;
    char *cwd;
    int errnum;
    // struct passwd *p = getpwuid(getuid());  // Check for NULL!
    long size = pathconf(".", _PC_PATH_MAX);
    char *dirbuf = (char *)malloc((size_t)size);
    size_t bytes_used = 0;

    // loop through the strings read via stdin and break at each \x00
    // Cookies, Query String, Post (via re-writting to stdin)

    char *cookie = (char *)malloc(MAX_CMDLINE_LEN);
    memset(cookie, 0, MAX_CMDLINE_LEN);

    // Get cookie value from /tmp/cookie.txt
    FILE *file = fopen("/tmp/cookie.txt", "r");

    if (file == NULL)
    {
        fprintf(stderr, "Failed to open the file.\n");
    }

    if (fgets(cookie, MAX_CMDLINE_LEN, file) == NULL)
    {
        fprintf(stderr, "Failed to read from the file.\n");
        fclose(file); // 파일 닫기
    }

    char *newline = strchr(cookie, '\n');
    if (newline != NULL)
    {
        *newline = '\0';
    }

    fclose(file);

    setenv(env_vars[0], cookie, 1);
    char *post_data = (char *)malloc(MAX_CMDLINE_LEN);
    memset(post_data, 0, MAX_CMDLINE_LEN);
    char *query_string = (char *)malloc(MAX_CMDLINE_LEN);
    memset(query_string, 0, MAX_CMDLINE_LEN);

    setenv(env_vars[1], query_string, 1);

    while (!*ptr)
    {
        bytes_used++;
        ptr++;
        rc++;
    }
    while (*ptr || bytes_used < bytes_read)
    {
        memcpy(saved_ptr, ptr, strlen(ptr) + 1);
        if (rc < 3)
        {
            load_variables(saved_ptr, rc);
        }
        if (rc < num_env_vars)
        {

            if (rc == 0)
            {
                strcat(cookie, "; ");
                strcat(cookie, saved_ptr);
                cookie = replace_char(cookie, '&', ';');
                setenv(env_vars[rc], cookie, 1);
            }
            else if (rc == 1)
            {
                strcat(query_string, "&");
                strcat(query_string, saved_ptr);

                setenv(env_vars[rc], query_string, 1);
            }
            else
            {

                setenv(env_vars[rc], saved_ptr, 1);
            }

            if (afl_area_ptr != NULL)
            {
                afl_area_ptr[0xffdd] = 1;
            }
        }
        else if (rc == num_env_vars)
        {
            char *json = getenv("DO_JSON");
            if (json)
            {
                saved_ptr = format_to_json(saved_ptr);
                debug_print(("\e[32m\tDONE JSON=%s\e[0m\n", saved_ptr));
            }

            real_content_length = write(pipefds[1], saved_ptr, strlen(saved_ptr));
            write(pipefds[1], "\n", 1);

            // debug_print(("\tReading from %d and writing %d bytes to %d \n", real_content_length, pipefds[0], pipefds[1]));
            // debug_print(("\t%-15s = \033[33m%s\033[0m \n", "POST", saved_ptr));

            char snum[20];
            sprintf(snum, "%d", real_content_length);
            memcpy(post_data, saved_ptr, strlen(saved_ptr) + 1);
            setenv("E", saved_ptr, 1);
            setenv("CONTENT_LENGTH", snum, 1);
        }

        rc++;
        while (*ptr)
        {
            ptr++;
            bytes_used++;
        }
        ptr++;
        bytes_used++;
    }
    debug_print(("[\e[32mWitcher\e[0m] %lib read / %lib used \n", bytes_read, bytes_used));
    if (afl_area_ptr != NULL)
    {
        afl_area_ptr[0xffdd] = 1;
    }
    if (cookie)
    {
        debug_print(("\t%-14s = \e[33m %s\e[0m\n", "COOKIES", cookie));
    }
    if (query_string)
    {
        debug_print(("\t%-14s = \e[33m %s\e[0m\n", "QUERY_STRING", query_string));
    }
    if (post_data)
    {
        debug_print(("\t%-9s (%s) = \e[33m %s\e[0m\n", "POST_DATA", getenv("CONTENT_LENGTH"), post_data));
    }
    debug_print(("\n"));

    free(saved_ptr);
    free(cookie);
    free(query_string);
    free(post_data);

    close(pipefds[0]);
    close(pipefds[1]);
#ifdef WITCHER_DEBUG
    fclose(logfile);
#endif

    fflush(stderr);
}
/************************************************************************************************/
/********************************** HTTP direct **************************************************/
/************************************************************************************************/
void afl_error_handler(int nSignum)
{
    printf("afl_error_handler()\n");
    FILE *elog = fopen("/tmp/witcher.log", "a+");
    if (elog)
    {
        fprintf(elog, "\033[36m[Witcher] detected error in child but AFL_META_INFO_ID is not set. !!!\033[0m\n");
        fclose(elog);
    }
}

/************************************************************************************************/
/********************************** END HTTP direct **************************************************/
/************************************************************************************************/

unsigned char *cgi_get_shm_mem(char *ch_shm_id)
{
    printf("cgi_get_shm_mem()\n");
    char *id_str;
    int shm_id;

    if (afl_area_ptr == NULL)
    {
        id_str = getenv(SHM_ENV_VAR);
        if (id_str)
        {
            shm_id = atoi(id_str);
            afl_area_ptr = shmat(shm_id, NULL, 0);
        }
        else
        {

            afl_area_ptr = malloc(MAPSIZE);
        }
    }
    return afl_area_ptr;
}

/**
 * The witcher init, is needed at the start of the script and is only executed once per child
 * it sets up the tracing enviornment
 */
void witcher_cgi_trace_init(char *ch_shm_id)
{
    printf("witcher_cgi_trace_init()\n");
    debug_print(("[\e[32mWitcher\e[0m] in Witcher trace\n\t\e[34mSCRIPT_FILENAME=%s\n\t\e[34mAFL_PRELOAD=%s\n\t\e[34mLD_LIBRARY_PATH=%s\e[0m\n", getenv("SCRIPT_FILENAME"), getenv("AFL_PRELOAD"), getenv("LD_LIBRARY_PATH"), getenv("LOGIN_COOKIE")));

    if (getenv("WC_INSTRUMENTATION"))
    {
        start_tracing = true;
        debug_print(("[Witcher] \e[32m WC INSTUMENTATION ENABLED \e[0m "));
    }
    else
    {
        debug_print(("[Witcher] WC INSTUMENTATION DISABLED "));
    }

    if (getenv("NO_WC_EXTRA"))
    {
        wc_extra_instr = false;
        debug_print((" WC Extra Instrumentation DISABLED \n"));
    }
    else
    {
        debug_print((" \e[32m WC Extra Instrumentation ENABLED \e[0m\n"));
    }
    top_pid = getpid();
    cgi_get_shm_mem(SHM_ENV_VAR);

    char *id_str = getenv(SHM_ENV_VAR);
    prefork_cgi_setup();
    if (id_str)
    {
        afl_forkserver();
        debug_print(("[\e[32mWitcher\e[0m] Returning with pid %d \n\n", getpid()));
    }
    // setup cgi must be after fork
    setup_cgi_env();

    // fflush(stdout);
}

// =================== trace values =================

typedef struct
{
    int opcode;

    int op1_type;
    int op1_val;

    int op2_type;
    int op2_val;

    int ret_type;
    int ret_val;

    // Constant 값 저장
    char *op1_cst;
    char *op2_cst;
    char *ret_cst;

} trace_data;

static pthread_t trace_thread_id;

static int trace_run;
static int thread_trace_state;

#define TRACE_DATA_SIZE 1024 * 1024 * 2
static struct trace_data *td[TRACE_DATA_SIZE];

static int trace_data_cur;
static int trace_data_size;

enum
{
    RUN = 1,
    STOP = 0
};
// ==================================================

void witcher_cgi_trace_finish()
{
    printf("witcher_cgi_trace_finish()\n");
    start_tracing = false;

    if (witcher_print_op)
    {
        char logfn[50];
        sprintf(logfn, "/tmp/trace-%s.dat", witcher_print_op);
        FILE *tout_fp = fopen(logfn, "a");
        setbuf(tout_fp, NULL);
        int cnt = 0;
        for (int x = 0; x < MAPSIZE; x++)
        {
            if (afl_area_ptr[x] > 0)
            {
                cnt++;
            }
        }
        fprintf(tout_fp, "BitMap has %d  \n", cnt);

        for (int x = 0; x < MAPSIZE; x++)
        {
            if (afl_area_ptr[x] > 0)
            {
                fprintf(tout_fp, "%04x ", x);
            }
        }
        fprintf(tout_fp, "\n");
        for (int x = 0; x < MAPSIZE; x++)
        {
            if (afl_area_ptr[x] > 0)
            {
                fprintf(tout_fp, " %02x  ", afl_area_ptr[x]);
            }
        }
        fprintf(tout_fp, "\n");

        // fprintf(logfile2,"\tAFTER match=%d afl=%d \n", matchcnt, afl_area_ptr[bitmapLoc]);

        fclose(tout_fp);
    }

    op = 0;
    last = 0;
    trace_index = 0;

    // trace Thread 종료
    while (trace_data_cur < trace_data_size)
    {
        ;
    }

    thread_trace_state = STOP;
    if (pthread_join(trace_thread_id, NULL) != 0)
    {
        printf("thread 종료 에러\n");
    }
}

// ============== trace 필요한 변수들 ==============

typedef struct
{
    int type;
    int value;
} save_value;

typedef struct
{
    char *type;
    char *value;

    int is_trace;

    int loop_len;
    save_value loop[512];
} type_trace;

static int trace_len;
static type_trace wt[512];

static int trace_check;

static int is_add_return;
static int enter_func;

static save_value new_ret;

static int save_vars_length;
static save_value save_vars[512];

static int return_count;
static int check_u_func;

static char *func_name;

static int global_print;

// get, post 작업중인 wt
static int work_wt_cur;
// ================================================
// trace 코드

bool check_type(char *type)
{
    const char *check[] = {"_GET", "_POST", "_REQUEST"};

    for (int i = 0; i < 3; i++)
    {
        // printf("%d == %d\n", strlen(type), strlen(check[i]));
        if (strlen(type) != strlen(check[i]))
            continue;

        bool loop_check = true;
        for (int j = 0; j < strlen(check[i]); j++)
        {
            // printf("%c == %c\n", type[j], check[i][j]);
            if (type[j] != check[i][j])
                loop_check = false;
        }

        if (loop_check)
            return true;
    }

    return false;
}

bool check_trace_val(type_trace wt, int type, int val)
{
    if (type == 0 || type == 1)
    {
        return true;
    }

    for (int i = 0; i < wt.loop_len; i++)
    {
        if (wt.loop[i].type == type && wt.loop[i].value == val)
            return true;
    }
    return false;
}

// enum
// {
//     NONE = "",
//     SQLI = "SQLI",
//     SSRF = "SSRF",
//     FILEUPLOAD = "FileUpload",
//     FILEDOWNLOAD = "FileDownload",
//     FILEDELETION = "FileDeletion",
//     XSS = "XSS",
//     CMDI = "CMDI"
// };

#define NONE ""
#define SQLI "SQLI"
#define SSRF "SSRF"
#define FILEUPLOAD "FileUpload"
#define FILEDOWNLOAD "FileDownload"
#define FILEDELETION "FileDeletion"
#define XSS "XSS"
#define CMDI "CMDI"

typedef struct
{
    char *func;
    char *vulntype;
} check_func;

static check_func cf;
// 함수 비교
check_func check_func_name(char *name)
{
    check_func tmp;
    const check_func check_list[] = {
        {"mysqli_query", SQLI},
        {"mysqli_multi_query", SQLI},
        {"query", SQLI},
        {"exec", SQLI},
        {"prepare", SQLI},
        {"query", SQLI},
        {"pg_execute", SQLI},
        {"pg_query", SQLI},
        {"pg_query_params", SQLI},
        {"find", SQLI},
        {"findOne", SQLI},
        {"findAndModify", SQLI},
        {"drop", SQLI},
        {"insert", SQLI},
        {"update", SQLI},
        {"file_get_contents", SSRF},
        {"curl_exec", SSRF},
        {"file", FILEUPLOAD},
        {"move_uploaded_file", FILEUPLOAD},
        {"copy", FILEUPLOAD},
        {"readfile", FILEDOWNLOAD},
        {"unlink", FILEDELETION},
        {"echo", XSS},
        {"eval", XSS}};

    // 입력된 이름과 배열 내의 문자열들 비교
    for (int i = 0; i < 24; i++)
    {
        if (strcmp(name, check_list[i].func) == 0)
        {
            tmp.func = check_list[i].func;
            tmp.vulntype = check_list[i].vulntype;
            return tmp;
        }
    }

    tmp.func = "";
    tmp.vulntype = "";

    return tmp;
}

// type : _GET, _POST
// value

#define DICTFILE "/tmp/dict.txt"
void saveDict(char *type, char *value)
{
    // printf("saveDict\n");

    FILE *file = fopen(DICTFILE, "a+");
    if (file)
    {
        fprintf(file, "%s\t\t%s\n", type, value);
        fclose(file);
    }
}

// Trace 저장
#define TRACEFILE "/tmp/tracelog.txt"
void saveTrace(type_trace _wt, check_func _cf)
{
    // printf("saveTrace\n");

    FILE *file = fopen(TRACEFILE, "a+");
    if (file)
    {
        fprintf(file, "%s\t\t%s\t\t%s\t\t%s\n", _wt.type, _wt.value, _cf.func, _cf.vulntype);
        fclose(file);
    }
}

void trace_run_func(trace_data *_td)
{
    if (global_print)
    {
        printf("\t=============================================\n");
        printf("\tfunc : %s(%d)\n", zend_get_opcode_name(_td->opcode), _td->opcode);
        printf("\top1 : %d %d %s\n", _td->op1_type, _td->op1_val, _td->op1_cst ? _td->op1_cst : "");
        printf("\top2 : %d %d %s\n", _td->op2_type, _td->op2_val, _td->op2_cst ? _td->op2_cst : "");
        printf("\tret : %d %d %s\n", _td->ret_type, _td->ret_val, _td->ret_cst ? _td->ret_cst : "");
        printf("\t=============================================\n");
    }

    // 추적 시작
    int opcode = _td->opcode;
    trace_data *pre_td;

    //
    char *xsstmp;

    // 값 할당 추적 용 코드
    if (opcode == ZEND_ASSIGN && trace_check == 1)
    {
        // 추적 시작

        wt[trace_len].is_trace = 1;

        wt[trace_len].loop_len = 0;
        int i = wt[trace_len].loop_len;

        wt[trace_len].loop[i].type = _td->op1_type;
        wt[trace_len].loop[i].value = _td->op1_val;
        wt[trace_len].loop_len++;

        trace_len++;
        trace_check = 0;
    }
    else if (trace_check)
    {
        trace_check = 0;
        return;
    }

    switch (opcode)
    {
    /* ZEND_FETCH_DIM_R
    _GET, _POST 추출 및 트레이싱 활성화

    1. 이전 opcode가 ZEND_FETCH_R일 경우, 해당 opcode의 인자에서 _GET, _POST 추출
    2. 현재 opcode에서 파라미터 값을 추출
    */
    case ZEND_FETCH_DIM_R:
        // printf("ZEND_FETCH_DIM_R\n");
        pre_td = td[trace_data_cur - 1];
        // printf("%d, %s, %s\n", pre_td->opcode, pre_td->op1_cst, _td->op2_cst);
        if (pre_td->opcode == ZEND_FETCH_R && pre_td->op1_cst != NULL && _td->op2_cst != NULL)
        {
            // _타입['값']
            char *type = pre_td->op1_cst;
            char *value = _td->op2_cst;

            // type이 _GET, _POST인지 여부 확인
            if (check_type(type))
            {
                // printf("\t\t_%s[%s]\n", type, value);

                // dict.txt 저장
                saveDict(type, value);

                // 트레이싱 등록, ZEND_ASSIGN에서 초기 추적을 시작해야함
                trace_check = 1;
                wt[trace_len].type = type;
                wt[trace_len].value = value;
            }
        }
        break;

    case ZEND_NEW:
        enter_func = 3;

        new_ret.type = _td->ret_type;
        new_ret.value = _td->ret_val;

        break;

    // 함수 진입 함수
    case ZEND_INIT_METHOD_CALL:
    case ZEND_INIT_FCALL_BY_NAME:
    case ZEND_INIT_FCALL:

        if (_td->op2_cst == NULL)
            break;

        enter_func = 1;

        // printf("\t 함수 호출 : %s\n", _td->op2_cst);

        // [TODO] 문자열 비교 필요
        // 찾을 경우, enter_func = 2
        cf = check_func_name(_td->op2_cst);
        if (cf.vulntype != "")
        {
            enter_func = 2;
            // 탐지가 되었음
            func_name = _td->op2_cst;

            // printf("\t 함수 탐지 %s ,type : %d\n", func_name, cf.vulntype);
            break;
        }

        // get, post 함수로 얻는 경우.. 새로운 트레이싱

        char *get_post_func[] = {"get", "post"};
        bool get_post_check = false;
        for (int i = 0; i < 2; i++)
        {
            if (strlen(_td->op2_cst) != strlen(get_post_func[i]))
                continue;

            bool lcheck = true;
            for (int j = 0; j < strlen(get_post_func[i]); j++)
            {
                //printf("%c == %c\n", _td->op2_cst[j], get_post_func[i][j]);
                if (_td->op2_cst[j] != get_post_func[i][j])
                    lcheck = false;
            }

            if (lcheck)
                get_post_check = true;
        }

        //printf("비교\n");
        if (get_post_check)
        {
            //printf("get post start trace\n");
            
            enter_func = 4;

            work_wt_cur = trace_len;
            wt[work_wt_cur].type = _td->op2_cst;

            if (_td->ret_type != 0)
            {
                wt[work_wt_cur].loop[wt[work_wt_cur].loop_len].type = _td->ret_type;
                wt[work_wt_cur].loop[wt[work_wt_cur].loop_len].value = _td->ret_val;
                wt[work_wt_cur].loop_len++;
            }
            // value는 VAR에서 채워야함
        }
        break;

    // XSS 탐지
    case ZEND_ECHO:
        xsstmp = "echo";
        cf = check_func_name(xsstmp);

        for (int i = 0; i < trace_len; i++)
        {
            bool trace_check = false;
            for (int j = 0; j < wt[i].loop_len; j++)
            {
                if (wt[i].loop[j].type == _td->op1_type &&
                    wt[i].loop[j].value == _td->op1_val)
                {
                    trace_check = true;
                }
            }

            if (trace_check)
            {
                // printf("==========\n");
                // printf("trace done\n");
                // printf("%s %d\n", cf.func, cf.vulntype);
                // printf("==========\n");

                saveTrace(wt[i], cf);

                wt[i].is_trace = false;
            }
        }
        break;

    case ZEND_INCLUDE_OR_EVAL:
        xsstmp = "eval";
        cf = check_func_name(xsstmp);

        for (int i = 0; i < trace_len; i++)
        {
            bool trace_check = false;
            for (int j = 0; j < wt[i].loop_len; j++)
            {
                if (wt[i].loop[j].type == _td->op1_type &&
                    wt[i].loop[j].value == _td->op1_val)
                {
                    trace_check = true;
                }
            }

            if (trace_check)
            {
                // printf("==========\n");
                // printf("trace done\n");
                // printf("%s %d\n", cf.func, cf.vulntype);
                // printf("==========\n");

                saveTrace(wt[i], cf);

                wt[i].is_trace = false;
            }
        }
        break;

    // ZEND_SEND_VAR 추적
    case ZEND_SEND_VAR_EX:
    //printf("ZEND_SEND_VAR_EX, %d\n", enter_func); 
    goto _ZEND_SEND_VAR;
    case ZEND_SEND_VAL_EX:
    case ZEND_SEND_VAL:
    case ZEND_SEND_VAR:
        _ZEND_SEND_VAR:
         //printf("ZEND_SNED_VAR, %d\n", enter_func); 
    
        switch (enter_func)
        {
        case 1:
            // ZEND_DO_FCALL
            // ZEND_DO_ICALL
            // 리턴 값 추적 용으로 저장해야 함

            // op1 - 짝수
            save_vars[save_vars_length].type = _td->op1_type;
            save_vars[save_vars_length].value = _td->op1_val;
            save_vars_length++;
            // ret - 홀수
            save_vars[save_vars_length].type = _td->ret_type;
            save_vars[save_vars_length].value = _td->ret_val;
            save_vars_length++;

            break;
        case 2:
            // TODO 추적

            // op1
            for (int i = 0; i < trace_len; i++)
            {
                bool trace_check = false;
                for (int j = 0; j < wt[i].loop_len; j++)
                {
                    if (wt[i].loop[j].type == _td->op1_type &&
                        wt[i].loop[j].value == _td->op1_val)
                    {
                        trace_check = true;
                    }
                }

                if (trace_check)
                {
                    // printf("==========\n");
                    // printf("trace done\n");
                    // printf("%s %d\n", cf.func, cf.vulntype);
                    // printf("==========\n");

                    saveTrace(wt[i], cf);

                    wt[i].is_trace = false;
                }
            }

            break;
        case 3:
            for (int i = 0; i < trace_len; i++)
            {
                for (int j = 0; j < wt[i].loop_len; j++)
                {
                    if (
                        (wt[i].loop[j].type == _td->op1_type) &&
                        (wt[i].loop[j].value == _td->op1_val))
                    {
                        // 한번더 등록되는 경우가 있음
                        bool check_duplicates = false;
                        for (int z = j; z < wt[i].loop_len; z++)
                        {
                            if (
                                (wt[i].loop[z].type == new_ret.type) &&
                                (wt[i].loop[z].value == new_ret.value))
                            {
                                check_duplicates = true;
                            }
                        }

                        // 중복 X
                        if (!check_duplicates)
                        {
                            if (!check_trace_val(wt[i], new_ret.type, new_ret.value))
                            {
                                wt[i].loop[wt[i].loop_len].type = new_ret.type;
                                wt[i].loop[wt[i].loop_len].value = new_ret.value;
                                wt[i].loop_len++;
                            }
                        }
                    }
                }
            }
            break;

        case 4:
            // 새로운 get, post 함수로 파라미터 추적?

            // 파라미터 추출
            //printf("%d, %s\n", _td->op1_type, _td->op1_cst);
            if (_td->op1_type == 1 && _td->op1_cst)
            {
                //printf("파라미터 추출 %s\n", _td->op1_cst);
                wt[work_wt_cur].value = _td->op1_cst;

                wt[work_wt_cur].is_trace = true;
                trace_len++;

                saveDict(wt[work_wt_cur].type, wt[work_wt_cur].value);

            }
            break;
        }
        break;

    case ZEND_DO_FCALL:
        return_count++;

        if (enter_func == 1)
        {
            // printf("enter_func = 1\n");
            for (int e = 0; e < save_vars_length; e++)
            {
                for (int i = 0; i < trace_len; i++)
                {
                    bool loop_check = false;
                    for (int j = 0; j < wt[i].loop_len; j++)
                    {
                        if ((save_vars[e].type == wt[i].loop[j].type) && (save_vars[e].value == wt[i].loop[j].value))
                        {
                            loop_check = true;
                        }
                    }
                    if (loop_check)
                    {
                        if (!check_trace_val(wt[i], _td->ret_type, _td->ret_val))
                        {
                            wt[i].loop[wt[i].loop_len].type = _td->ret_type;
                            wt[i].loop[wt[i].loop_len].value = _td->ret_val;
                            wt[i].loop_len++;
                        }
                    }
                }
            }
        }
        if(enter_func == 4){
            // 리턴값도 넣어주자
            if (_td->ret_type != 0)
            {
                wt[work_wt_cur].loop[wt[work_wt_cur].loop_len].type = _td->ret_type;
                wt[work_wt_cur].loop[wt[work_wt_cur].loop_len].value = _td->ret_val;
                wt[work_wt_cur].loop_len++;
            }
        }

        enter_func = 0;
        save_vars_length = 0;

        break;
    case ZEND_DO_ICALL:
        if (enter_func == 1)
        {
            // printf("enter_func = 1\n");
            for (int e = 0; e < save_vars_length; e++)
            {
                for (int i = 0; i < trace_len; i++)
                {
                    bool loop_check = false;
                    for (int j = 0; j < wt[i].loop_len; j++)
                    {
                        if ((save_vars[e].type == wt[i].loop[j].type) && (save_vars[e].value == wt[i].loop[j].value))
                        {
                            loop_check = true;
                        }
                    }
                    if (loop_check)
                    {
                        if (!check_trace_val(wt[i], _td->ret_type, _td->ret_val))
                        {
                            wt[i].loop[wt[i].loop_len].type = _td->ret_type;
                            wt[i].loop[wt[i].loop_len].value = _td->ret_val;
                            wt[i].loop_len++;
                        }
                    }
                }
            }
        }

        enter_func = 0;
        save_vars_length = 0;

        break;
    case ZEND_DO_UCALL:

        switch (enter_func)
        {
        case 1:
            is_add_return = 0;
            for (int e = 0; e < save_vars_length; e += 2)
            {
                for (int i = 0; i < trace_len; i++)
                {
                    bool loop_check = false;
                    for (int j = 0; j < wt[i].loop_len; j++)
                    {
                        if (save_vars[e].type == wt[i].loop[j].type &&
                            save_vars[e].value == wt[i].loop[j].type)
                        {
                            is_add_return = i;
                            loop_check = true;
                        }
                    }

                    if (loop_check && (is_add_return == i) && ((e % 2) == 0))
                    {
                        if (!check_trace_val(wt[i], save_vars[e + 1].type, save_vars[e + 1].value))
                        {
                            wt[i].loop[wt[i].loop_len].type = save_vars[e + 1].type;
                            wt[i].loop[wt[i].loop_len].value = save_vars[e + 1].value;

                            wt[i].loop_len++;
                        }
                        is_add_return++;
                    }

                    if (!check_trace_val(wt[i], _td->ret_type, _td->ret_val))
                    {
                        wt[i].loop[wt[i].loop_len].type = _td->ret_type;
                        wt[i].loop[wt[i].loop_len].value = _td->ret_val;
                        wt[i].loop_len++;
                    }
                }
            }
            break;

        case 4:
            // 리턴값도 넣어주자
            if (_td->ret_type != 0)
            {
                wt[work_wt_cur].loop[wt[work_wt_cur].loop_len].type = _td->ret_type;
                wt[work_wt_cur].loop[wt[work_wt_cur].loop_len].value = _td->ret_val;
                wt[work_wt_cur].loop_len++;
            }
            break;
        }

        enter_func = 0;
        save_vars_length = 0;
        break;

    case ZEND_RETURN:
        if (return_count-- == 0)
        {
            printf("초기화 진행\n");
            for (int i = 0; i < trace_len; i++)
            {
                free(td[i]);
            }
            trace_len = 0;
        }
        break;

    // 모든 함수에 대하여 추적
    default:
        // for (int i = 0; i < trace_len; i++)
        // {
        //     for (int j = 0; j < wt[i].loop_len; j++)
        //     {
        //         if (!check_trace_val(wt[i], _td->op1_type, _td->op1_val))
        //         {
        //             wt[i].loop[j].type = _td->op1_type;
        //             wt[i].loop[j].value = _td->op1_val;
        //             wt[i].loop_len++;
        //         }
        //         if (!check_trace_val(wt[i], _td->op2_type, _td->op2_val))
        //         {
        //             wt[i].loop[j].type = _td->op2_type;
        //             wt[i].loop[j].value = _td->op2_val;
        //             wt[i].loop_len++;
        //         }
        //         if (!check_trace_val(wt[i], _td->ret_type, _td->ret_val))
        //         {
        //             wt[i].loop[j].type = _td->ret_type;
        //             wt[i].loop[j].value = _td->ret_val;
        //             wt[i].loop_len++;
        //         }
        //     }
        // }
        for (int i = 0; i < trace_len; i++)
        {
            int arg_check = 0;
            for (int j = 0; j < wt[i].loop_len; j++)
            {
                // 이제부터 모든 opcode의 파라미터들을 감시해야함
                // op1

                if ((_td->op1_type != 0x0))
                {
                    if ((wt[i].loop[j].value == _td->op1_val) &&
                        wt[i].loop[j].type == _td->op1_type)
                    {
                        arg_check += (1 << 0);
                    }
                }

                // op2
                if ((_td->op2_type != 0x0))
                {
                    if ((wt[i].loop[j].value == _td->op2_val) &&
                        wt[i].loop[j].type == _td->op2_type)
                    {
                        arg_check += (1 << 1);
                    }
                }

                // ret
                if ((_td->ret_type != 0x0))
                {
                    if ((wt[i].loop[j].value == _td->ret_val) &&
                        wt[i].loop[j].type == _td->ret_type)
                    {
                        arg_check += (1 << 2);
                    }
                }
            }

            switch (arg_check)
            {
            case 0:
                break;
            case 1: // op2, ret

                if ((_td->op2_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->op2_type;
                    wt[i].loop[wt[i].loop_len].value = _td->op2_val;
                    wt[i].loop_len++;
                }
                if ((_td->ret_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->ret_type;
                    wt[i].loop[wt[i].loop_len].value = _td->ret_val;
                    wt[i].loop_len++;
                }

                break;
            case 2: // op1, ret
                if ((_td->op1_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->op1_type;
                    wt[i].loop[wt[i].loop_len].value = _td->op1_val;
                    wt[i].loop_len++;
                }
                if ((_td->ret_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->ret_type;
                    wt[i].loop[wt[i].loop_len].value = _td->ret_val;
                    wt[i].loop_len++;
                }

                break;
            case 4: // op1, op2
                if ((_td->op2_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->op2_type;
                    wt[i].loop[wt[i].loop_len].value = _td->op2_val;
                    wt[i].loop_len++;
                }
                if ((_td->op1_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->op1_type;
                    wt[i].loop[wt[i].loop_len].value = _td->op1_val;
                    wt[i].loop_len++;
                }
                break;

            case 3: // ret
                if ((_td->ret_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->ret_type;
                    wt[i].loop[wt[i].loop_len].value = _td->ret_val;
                    wt[i].loop_len++;
                }
                break;
            case 5: // op2
                if ((_td->op2_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->op2_type;
                    wt[i].loop[wt[i].loop_len].value = _td->op2_val;
                    wt[i].loop_len++;
                }
                break;
            case 6: // op1
                if ((_td->op1_type != 0x0))
                {
                    wt[i].loop[wt[i].loop_len].type = _td->op1_type;
                    wt[i].loop[wt[i].loop_len].value = _td->op1_val;
                    wt[i].loop_len++;
                }
                break;

            case 7:
                break;
            }
        }
        break;
    }

    // 트레이스 리스트 출력

    if (global_print)
    {
        for (int i = 0; i < trace_len; i++)
        {
            printf("\t==trace list==");
            printf("\t$%s[%s]\n", wt[i].type, wt[i].value);

            for (int j = 0; j < wt[i].loop_len; j++)
            {
                printf("\t [%d]%d\n", wt[i].loop[j].type, wt[i].loop[j].value);
            }
            printf("\t==============");
        }
    }

    // TODO 수정해야함
    for (int i = 0; i < trace_len; i++)
    {
        for (int j = wt[i].loop_len - 1; j >= 0; j--)
        {
            if (wt[i].loop[j].type == 0 || wt[i].loop[j].type == 1)
            {
                wt[i].loop_len--;
            }
        }
    }
}

void *thread_trace_func(void *arg)
{
    printf("thread start\n");
    while (thread_trace_state == RUN)
    {
        // trace_data 대기
        while (trace_data_cur == trace_data_size)
        {
            if (thread_trace_state == STOP)
                return;
        }

        trace_data *tmp_td = td[trace_data_cur];
        trace_run_func(tmp_td);

        trace_data_cur++;

        // sleep(10);
    }
    printf("thread stop\n");

    return;
}

static int issue_check = 0;

void vld_start_trace()
{

    return;

    if (getenv("ST"))
    {
        trace_run = RUN;
        thread_trace_state = RUN;

        // 트레이싱 쓰레드 생성
        if (pthread_create(&trace_thread_id, NULL, thread_trace_func, NULL) != 0)
        {
            printf("can't create Thread\n");

            trace_run = STOP;
            thread_trace_state = STOP;
        }

        if (getenv("PR"))
            global_print = 1;

        // 코드 커버리지 계측
        if (afl_area_ptr == NULL)
        {
            if (getenv(SHM_ENV_VAR))
            {
                int shm_id = atoi(getenv(SHM_ENV_VAR));
                afl_area_ptr = shmat(shm_id, NULL, 0);
            }
        }

        // =================
    }
}

char *getConstant(zend_op *opline, int opline_arg_type, int opline_arg_val)
{
    switch (opline_arg_type)
    {
    case IS_CONST:
        switch (((zval *)((char *)opline + opline_arg_val))->u1.v.type)
        {
        case IS_STRING:
            return ((zval *)((char *)opline + opline_arg_val))->value.str->val;
            break;
        }
        break;
    }

    return NULL;
}

static int optimization_flag;

void vld_external_trace(zend_execute_data *execute_data, const zend_op *opline)
{

    if (trace_run == 0)
    {
        if (issue_check == 0)
        {
            FILE *file;

            // 파일 경로 설정
            char *filename = "/tmp/tracestart";

            // 파일 열기 시도
            file = fopen(filename, "r");
            if (file != NULL)
            {
                trace_run = RUN;
                thread_trace_state = RUN;

                // 트레이싱 쓰레드 생성
                if (pthread_create(&trace_thread_id, NULL, thread_trace_func, NULL) != 0)
                {
                    printf("can't create Thread\n");

                    trace_run = STOP;
                    thread_trace_state = STOP;
                }

                if (getenv("PR"))
                    global_print = 1;

                // 코드 커버리지 계측
                if (afl_area_ptr == NULL)
                {
                    if (getenv(SHM_ENV_VAR))
                    {
                        int shm_id = atoi(getenv(SHM_ENV_VAR));
                        afl_area_ptr = shmat(shm_id, NULL, 0);
                    }
                }

                issue_check = 1;
            }
        }

        if (issue_check == 0)
        {
            return;
        }
        // =================
    }

    // if (trace_run == 1)
    // {
    //     // OFF를 원한다면..
    //     FILE *file;

    //     // 파일 경로 설정
    //     char *filename = "/tmp/tracestart";

    //     // 파일 열기 시도
    //     file = fopen(filename, "r");

    //     // 파일을 지우면 더이상 트레이싱을 진행하지 않음
    //     if (file == NULL)
    //     {
    //     }
    // }

    // 코드 커버리지 계측
    op = (opline->lineno << 8) | opline->opcode; // opcode; //| (lineno << 8);

    int bitmapLoc = (op ^ last) % MAPSIZE;
    // printf("bitmapLoc : %x \n", bitmapLoc);

    // fprintf(ofile, "==============================\n");

    if (afl_area_ptr != NULL)
        afl_area_ptr[bitmapLoc]++;

    last = op;
    // ====================

    char *opname;
    if (global_print)
    {
        opname = zend_get_opcode_name(opline->opcode);
        printf("%s[%d](%d[%d], %d[%d]) => %d[%d]\n",
               opname, opline->opcode,
               opline->op1, opline->op1_type,
               opline->op2, opline->op2_type,
               opline->result, opline->result_type);

        FILE *file = fopen("/tmp/opcodeLog", "a+");
        if (file)
        {

            fprintf(file, "%s[%d](%d[%d], %d[%d]) => %d[%d]\n",
                    opname, opline->opcode,
                    opline->op1, opline->op1_type,
                    opline->op2, opline->op2_type,
                    opline->result, opline->result_type);
        }
    }

    // 값 저장

    // 중간 테스트
    // printf("=============================================\n");
    // printf("func : %s(%d)\n", zend_get_opcode_name(tmp_td->opcode), tmp_td->opcode);
    // printf("op1 : %d %d %s\n", tmp_td->op1_type, tmp_td->op1_val, tmp_td->op1_cst ? tmp_td->op1_cst : "");
    // printf("op2 : %d %d %s\n", tmp_td->op2_type, tmp_td->op2_val, tmp_td->op2_cst ? tmp_td->op2_cst : "");
    // printf("ret : %d %d %s\n", tmp_td->ret_type, tmp_td->ret_val, tmp_td->ret_cst ? tmp_td->ret_cst : "");
    // printf("=============================================\n");

    // TODO 모든걸 저장하면 버퍼가 터짐
    // 트레이싱 상태 플래그일때만 저장하기로?

    // _GET, 얻는 패턴 일떄?
    // printf("trace_data : %d\n", trace_data_size);

    // TODO _GET, _POST 형식만.. 저장되게
    /*
                ZEND_FETCH_R[80](896[1], -1[0]) => 160[2]
                ZEND_FETCH_DIM_R[81](160[2], 880[1]) => 176[2]
`   */
    trace_data *tmp_td;

    if (optimization_flag)
    {
        tmp_td = (trace_data *)malloc(sizeof(trace_data));

        tmp_td->opcode = opline->opcode;

        tmp_td->op1_type = opline->op1_type;
        tmp_td->op2_type = opline->op2_type;
        tmp_td->ret_type = opline->result_type;

        tmp_td->op1_val = opline->op1.var;
        tmp_td->op2_val = opline->op2.var;
        tmp_td->ret_val = opline->result.var;

        tmp_td->op1_cst = getConstant(opline, tmp_td->op1_type, tmp_td->op1_val);
        tmp_td->op2_cst = getConstant(opline, tmp_td->op2_type, tmp_td->op2_val);
        tmp_td->ret_cst = getConstant(opline, tmp_td->ret_type, tmp_td->ret_val);
        td[trace_data_size] = tmp_td;
        trace_data_size++;
    }

    if (optimization_flag == 0 && (opline->opcode == ZEND_INIT_METHOD_CALL ||
                                   opline->opcode == ZEND_INIT_FCALL_BY_NAME ||
                                   opline->opcode == ZEND_INIT_FCALL))
    {

        // get, post이면...
        char *test = getConstant(opline, opline->op2_type, opline->op2.var);
        if (test)
        {
            char *get_post_func[] = {"get", "post"};
            bool get_post_check = false;
            for (int i = 0; i < 2; i++)
            {
                if (strlen(test) != strlen(get_post_func[i]))
                    continue;

                bool lcheck = true;
                for (int j = 0; j < strlen(get_post_func[i]); j++)
                {
                    // printf("%c == %c\n", type[j], check[i][j]);
                    if (test[j] != get_post_func[i][j])
                        lcheck = false;
                }

                if (lcheck)
                    get_post_check = true;
            }

            if (get_post_check)
            {
                printf("트레이싱 시작 \n"); 
                tmp_td = (trace_data *)malloc(sizeof(trace_data));

                tmp_td->opcode = opline->opcode;

                tmp_td->op1_type = opline->op1_type;
                tmp_td->op2_type = opline->op2_type;
                tmp_td->ret_type = opline->result_type;

                tmp_td->op1_val = opline->op1.var;
                tmp_td->op2_val = opline->op2.var;
                tmp_td->ret_val = opline->result.var;

                tmp_td->op1_cst = getConstant(opline, tmp_td->op1_type, tmp_td->op1_val);
                tmp_td->op2_cst = getConstant(opline, tmp_td->op2_type, tmp_td->op2_val);
                tmp_td->ret_cst = getConstant(opline, tmp_td->ret_type, tmp_td->ret_val);
                td[trace_data_size] = tmp_td;
                trace_data_size++;

                optimization_flag = 1;
            }
        }
    }

    if (optimization_flag == 0 && opline->opcode == ZEND_FETCH_DIM_R && execute_data->opline->opcode == ZEND_FETCH_R)
    {
        zend_op *pre_opline = execute_data->opline;
        // _GET, _POST 비교
        char *test = getConstant(pre_opline, pre_opline->op1_type, pre_opline->op1.var);

        // printf("test : %s\n", test);
        if (check_type(test))
        {
            // printf("entered\n");
            //  pre opcode
            tmp_td = (trace_data *)malloc(sizeof(trace_data));

            tmp_td->opcode = pre_opline->opcode;

            tmp_td->op1_type = pre_opline->op1_type;
            tmp_td->op2_type = pre_opline->op2_type;
            tmp_td->ret_type = pre_opline->result_type;

            tmp_td->op1_val = pre_opline->op1.var;
            tmp_td->op2_val = pre_opline->op2.var;
            tmp_td->ret_val = pre_opline->result.var;

            tmp_td->op1_cst = getConstant(pre_opline, tmp_td->op1_type, tmp_td->op1_val);
            tmp_td->op2_cst = getConstant(pre_opline, tmp_td->op2_type, tmp_td->op2_val);
            tmp_td->ret_cst = getConstant(pre_opline, tmp_td->ret_type, tmp_td->ret_val);
            td[trace_data_size] = tmp_td;
            trace_data_size++;
            // --------------------------

            // cur opcode
            trace_data *tmp_td = (trace_data *)malloc(sizeof(trace_data));

            tmp_td->opcode = opline->opcode;

            tmp_td->op1_type = opline->op1_type;
            tmp_td->op2_type = opline->op2_type;
            tmp_td->ret_type = opline->result_type;

            tmp_td->op1_val = opline->op1.var;
            tmp_td->op2_val = opline->op2.var;
            tmp_td->ret_val = opline->result.var;

            tmp_td->op1_cst = getConstant(opline, tmp_td->op1_type, tmp_td->op1_val);
            tmp_td->op2_cst = getConstant(opline, tmp_td->op2_type, tmp_td->op2_val);
            tmp_td->ret_cst = getConstant(opline, tmp_td->ret_type, tmp_td->ret_val);
            td[trace_data_size] = tmp_td;
            trace_data_size++;

            // set optimization flag
            optimization_flag = 1;
        }
    }

    if (trace_data_size == TRACE_DATA_SIZE)
    {
        printf("트레이싱이 너무 오래 지속됩니다.\n");
    }
}
